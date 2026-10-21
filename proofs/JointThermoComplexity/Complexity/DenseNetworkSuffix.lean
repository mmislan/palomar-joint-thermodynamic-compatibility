module
public import proofs.JointThermoComplexity.Complexity.DenseDimensionProgram
public import proofs.JointThermoComplexity.Complexity.DataCodec
public import proofs.JointThermoComplexity.Complexity.RationalLiteralNetwork
public import proofs.JointThermoComplexity.Complexity.RepeatedOutput

set_option autoImplicit false
@[expose] public section

/-! A precompiled suffix reads only the retained structural dimensions.
Literal intervals use the original box codec and all work tapes are returned. -/

namespace JointThermoComplexity.Complexity.DenseNetworkSuffix
open _root_.Complexity _root_.Complexity.TM HeaderAt

inductive Part where
  | bits : List Bool → Part
  | copies : Fin 64 → List Bool → Part

def Part.machine : Part → TM 64
  | .bits word => emitBitsTM word
  | .copies port word => RepeatedOutput.machine port word
def Part.word (values : Fin 64 → ℕ) : Part → List Bool
  | .bits word => word
  | .copies port word => RepeatedOutput.copies word (values port)
def Part.time (values : Fin 64 → ℕ) : Part → ℕ
  | .bits word => word.length
  | .copies port word => values port * (word.length + 2) + (values port + 2)
def Part.Ready (values : Fin 64 → ℕ) (work : Fin 64 → Tape) : Part → Prop
  | .bits _ => True
  | .copies port _ => IsReg (values port) (work port)
def Part.ports : Part → List (Fin 64)
  | .bits _ => []
  | .copies port _ => [port]

theorem Part.run (part : Part) (values : Fin 64 → ℕ) (before input emitted : List Bool)
    (inp : Tape) (work : Fin 64 → Tape) (out : Tape) (hc : Cursor before input emitted inp work out)
    (hs : ∀ j, Parked (work j)) (hr : part.Ready values work) :
    ∃ d t, t ≤ part.time values ∧ part.machine.reachesIn t ⟨part.machine.qstart, inp, work, out⟩ d ∧
      part.machine.halted d ∧ Cursor before input (emitted ++ part.word values) d.input d.work d.output ∧ d.work = work := by
  cases part with
  | bits word =>
    obtain ⟨d, t, ht, hd, hh, hcur, _, he⟩ := FixedOutput.hoareTime word before input emitted (fun next => next = work)
      inp work out ⟨hc, hs, rfl⟩
    exact ⟨d, t, ht, hd, hh, hcur, he⟩
  | copies port word =>
    obtain ⟨d, t, ht, hd, hh, _, hcur, _, he⟩ := RepeatedOutput.hoareTime port (values port) before input emitted word
      (fun next => next = work) inp work out ⟨hr, hc, hs, rfl⟩
    exact ⟨d, t, ht, hd, hh, hcur, he⟩

def compile : List Part → TM 64
  | [] => emitBitsTM []
  | part :: rest => seqTM part.machine (compile rest)
def words (values : Fin 64 → ℕ) : List Part → List Bool
  | [] => []
  | part :: rest => part.word values ++ words values rest
def bound (values : Fin 64 → ℕ) : List Part → ℕ
  | [] => 0
  | part :: rest => part.time values + 1 + bound values rest
def Ready (program : List Part) (values : Fin 64 → ℕ) (work : Fin 64 → Tape) : Prop :=
  ∀ part ∈ program, part.Ready values work

theorem run (program : List Part) (values : Fin 64 → ℕ) (before input emitted : List Bool)
    (inp : Tape) (work : Fin 64 → Tape) (out : Tape) (hc : Cursor before input emitted inp work out)
    (hs : ∀ j, Parked (work j)) (hr : Ready program values work) :
    ∃ d t, t ≤ bound values program ∧ (compile program).reachesIn t ⟨(compile program).qstart, inp, work, out⟩ d ∧
      (compile program).halted d ∧ Cursor before input (emitted ++ words values program) d.input d.work d.output ∧ d.work = work := by
  induction program generalizing emitted inp work out with
  | nil => exact ⟨⟨(compile []).qhalt, inp, work, out⟩, 0, le_rfl, .zero, rfl,
      by simpa only [words, List.append_nil] using hc, rfl⟩
  | cons part rest ih =>
    obtain ⟨c, tc, htc, hcReach, hcHalt, hcCur, hcWork⟩ := part.run values before input emitted inp work out hc hs
      (hr part List.mem_cons_self)
    have hrRest : Ready rest values c.work := by
      intro p hp
      rw [hcWork]
      exact hr p (List.mem_cons_of_mem _ hp)
    obtain ⟨d, td, htd, hdReach, hdHalt, hdCur, hdWork⟩ := ih (emitted ++ part.word values) c.input c.work c.output hcCur
      (by simpa only [hcWork] using hs) hrRest
    obtain ⟨hi, hw, ho⟩ := hcCur.phase
    have hrr : (compile rest).reachesIn td ⟨(compile rest).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
      simpa only [hi, hw, ho] using hdReach
    refine ⟨phase2Wrap part.machine (compile rest) d, tc + 1 + td, by simp only [bound]; omega,
      seqTM_reachesIn_of_reachesIn _ _ hcReach hcHalt hrr, (phase2Wrap_halted_iff _ _ d).mpr hdHalt, ?_, hdWork.trans hcWork⟩
    simpa only [phase2Wrap, words, List.append_assoc] using hdCur

def internalWord : List Bool := (FiniteCodec.optional DataCodec.box).code (some RationalLiteralNetwork.internalBox)
def externalWord : List Bool := (FiniteCodec.optional DataCodec.box).code (some RationalLiteralNetwork.externalBox)
def common : List Part :=
  [.copies 34 [true], .copies 35 [false], .copies 33 [false], .copies 34 [true], .copies 34 [false],
    .bits [true, true], .copies 33 [false], .copies 35 [false], .copies 33 [true],
    .copies 34 [false], .copies 34 [true], .copies 37 [true]]
def program (boxed : Bool) : List Part := common ++
  if boxed then [.copies 34 internalWord, .copies 35 externalWord, .copies 33 internalWord] else [.copies 36 [false]]
def values (boxed : Bool) (n N : ℕ) (j : Fin 64) : ℕ :=
  if j = 33 then N else if j = 34 then N + 2 else if j = 35 then DenseDimensionProgram.result boxed n N 3
  else if j = 36 then DenseDimensionProgram.result boxed n N 4 else if j = 37 then DenseDimensionProgram.result boxed n N 5 else 0
def Dims (boxed : Bool) (n N : ℕ) (work : Fin 64 → Tape) : Prop := IsReg N (work 33) ∧ IsReg (N + 2) (work 34) ∧
  IsReg (DenseDimensionProgram.result boxed n N 3) (work 35) ∧ IsReg (DenseDimensionProgram.result boxed n N 4) (work 36) ∧
    IsReg (DenseDimensionProgram.result boxed n N 5) (work 37)

theorem program_ports : ∀ boxed : Bool, ∀ j : Fin 64, j ∈ (program boxed).flatMap Part.ports → j ∈ ([33, 34, 35, 36, 37] : List (Fin 64)) := by decide

theorem ready (boxed : Bool) (n N : ℕ) (work : Fin 64 → Tape) (hd : Dims boxed n N work) : Ready (program boxed) (values boxed n N) work := by
  have hreg (j : Fin 64) (hj : j ∈ ([33, 34, 35, 36, 37] : List (Fin 64))) : IsReg (values boxed n N j) (work j) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact hd.1
    · exact hd.2.1
    · exact hd.2.2.1
    · exact hd.2.2.2.1
    · exact hd.2.2.2.2
  intro part hp
  cases part with
  | bits word => trivial
  | copies port word =>
    exact hreg port (program_ports boxed port (List.mem_flatMap.mpr ⟨.copies port word, hp, by simp [Part.ports]⟩))

def machine (boxed : Bool) : TM 64 := compile (program boxed)
def word (boxed : Bool) (n N : ℕ) : List Bool := words (values boxed n N) (program boxed)
def timeBound (boxed : Bool) (n N : ℕ) : ℕ := bound (values boxed n N) (program boxed)
def Pre (boxed : Bool) (n N : ℕ) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Dims boxed n N work ∧ R work

theorem hoareTime (boxed : Bool) (n N : ℕ) (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) :
    (machine boxed).HoareTime (Pre boxed n N before input emitted R)
      (Pre boxed n N before input (emitted ++ word boxed n N) R) (timeBound boxed n N) := by
  rintro inp work out ⟨hc, hs, hd, hr⟩
  obtain ⟨d, t, ht, hdReach, hdHalt, hdCur, hdWork⟩ := run (program boxed) (values boxed n N) before input emitted inp work out hc hs (ready boxed n N work hd)
  exact ⟨d, t, ht, hdReach, hdHalt, hdCur, by simpa only [hdWork] using hs,
    by simpa only [hdWork] using hd, by simpa only [hdWork] using hr⟩

end JointThermoComplexity.Complexity.DenseNetworkSuffix

#print axioms JointThermoComplexity.Complexity.DenseNetworkSuffix.hoareTime
