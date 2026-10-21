module
public import proofs.JointThermoComplexity.Complexity.VariableFrame

set_option autoImplicit false
@[expose] public section

/-!
# Static syntax templates with runtime variable addresses

Each template is a fixed list of word and register-output instructions. Register
values are ghost parameters in the execution theorem, not inputs to machine
construction. This does not compile an input-dependent syntax tree into a new TM.
-/

namespace JointThermoComplexity.Complexity.OutputProgram
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax

variable {w : ℕ}

inductive Instruction (w : ℕ) where
  | word : List Bool → Instruction w
  | var : Fin w → Instruction w
  deriving DecidableEq

def Instruction.machine (scratch : Fin w) : Instruction w → TM w
  | .word bits => emitBitsTM bits
  | .var fuel => VariableOutput.machine fuel scratch

def Instruction.code (values : Fin w → ℕ) : Instruction w → List Bool
  | .word bits => bits
  | .var fuel => [false, false, true] ++ BitCodec.naturalCode (values fuel)

def Instruction.timeBound (values : Fin w → ℕ) : Instruction w → ℕ
  | .word bits => bits.length
  | .var fuel => VariableOutput.timeBound (values fuel)

def Instruction.Ready (values : Fin w → ℕ) (work : Fin w → Tape) : Instruction w → Prop
  | .word _ => True
  | .var fuel => IsReg (values fuel) (work fuel)

def Instruction.Valid (scratch : Fin w) : Instruction w → Prop
  | .word _ => True
  | .var fuel => fuel ≠ scratch

theorem Instruction.run (scratch : Fin w) (instruction : Instruction w) (values : Fin w → ℕ)
    (before input emitted : List Bool) (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before input emitted inp work out) (hs : ∀ j, Parked (work j))
    (hb : Register 0 (work scratch)) (hv : instruction.Valid scratch) (hr : instruction.Ready values work) :
    ∃ d t, t ≤ instruction.timeBound values ∧
      (instruction.machine scratch).reachesIn t ⟨(instruction.machine scratch).qstart, inp, work, out⟩ d ∧
      (instruction.machine scratch).halted d ∧
      Cursor before input (emitted ++ instruction.code values) d.input d.work d.output ∧ d.work = work := by
  cases instruction with
  | word bits =>
    obtain ⟨d, t, ht, hreach, hhalt, hdcur, _, hdwork⟩ :=
      FixedOutput.hoareTime bits before input emitted (fun work' => work' = work) inp work out ⟨hc, hs, rfl⟩
    exact ⟨d, t, ht, hreach, hhalt, hdcur, hdwork⟩
  | var fuel =>
    let idx : Fin (values fuel + 1) := ⟨values fuel, by omega⟩
    obtain ⟨d, t, ht, hreach, hhalt, hdcur, _, _, _, hdwork⟩ :=
      VariableFrame.hoareTime fuel scratch hv idx before input emitted (fun work' => work' = work)
        inp work out ⟨hc, hs, hr, hb, rfl⟩
    exact ⟨d, t, ht, hreach, hhalt,
      by simpa only [Instruction.code, Term.code] using hdcur, hdwork⟩

def machine (scratch : Fin w) : List (Instruction w) → TM w
  | [] => emitBitsTM []
  | instruction :: rest => seqTM (instruction.machine scratch) (machine scratch rest)

def code (values : Fin w → ℕ) : List (Instruction w) → List Bool
  | [] => []
  | instruction :: rest => instruction.code values ++ code values rest

def timeBound (values : Fin w → ℕ) : List (Instruction w) → ℕ
  | [] => 0
  | instruction :: rest => instruction.timeBound values + 1 + timeBound values rest

def Ready (program : List (Instruction w)) (values : Fin w → ℕ) (work : Fin w → Tape) : Prop :=
  ∀ instruction, instruction ∈ program → instruction.Ready values work

def Valid (program : List (Instruction w)) (scratch : Fin w) : Prop :=
  ∀ instruction, instruction ∈ program → instruction.Valid scratch

theorem run (scratch : Fin w) (program : List (Instruction w)) (values : Fin w → ℕ)
    (before input emitted : List Bool) (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before input emitted inp work out) (hs : ∀ j, Parked (work j))
    (hb : Register 0 (work scratch)) (hv : Valid program scratch) (hr : Ready program values work) :
    ∃ d t, t ≤ timeBound values program ∧
      (machine scratch program).reachesIn t ⟨(machine scratch program).qstart, inp, work, out⟩ d ∧
      (machine scratch program).halted d ∧
      Cursor before input (emitted ++ code values program) d.input d.work d.output ∧ d.work = work := by
  induction program generalizing emitted inp work out with
  | nil =>
    exact ⟨⟨(machine scratch []).qhalt, inp, work, out⟩, 0, le_rfl, .zero, rfl,
      by simpa only [code, List.append_nil] using hc, rfl⟩
  | cons instruction rest ih =>
    obtain ⟨c, tc, htc, hcreach, hchalt, hccur, hcwork⟩ :=
      Instruction.run scratch instruction values before input emitted inp work out hc hs hb
        (hv instruction (by simp)) (hr instruction (by simp))
    have hvrest : Valid rest scratch := fun i hi => hv i (List.mem_cons_of_mem _ hi)
    have hrrest : Ready rest values c.work := by
      intro i hi
      rw [hcwork]
      exact hr i (List.mem_cons_of_mem _ hi)
    obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdwork⟩ :=
      ih (emitted := emitted ++ instruction.code values) (inp := c.input) (work := c.work) (out := c.output)
        hccur (by simpa only [hcwork] using hs) (by simpa only [hcwork] using hb) hvrest hrrest
    obtain ⟨hi, hw, ho⟩ := hccur.phase
    have hrr : (machine scratch rest).reachesIn td
        ⟨(machine scratch rest).qstart, transitionInput c.input,
          (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
      simpa only [hi, hw, ho] using hdreach
    have hreach := seqTM_reachesIn_of_reachesIn (instruction.machine scratch) (machine scratch rest) hcreach hchalt hrr
    refine ⟨phase2Wrap (instruction.machine scratch) (machine scratch rest) d, tc + 1 + td,
      by simp only [timeBound]; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, ?_, hdwork.trans hcwork⟩
    simpa only [phase2Wrap, code, List.append_assoc] using hdcur

theorem hoareTime (scratch : Fin w) (program : List (Instruction w)) (values : Fin w → ℕ)
    (hv : Valid program scratch) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine scratch program).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work scratch) ∧ Ready program values work ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ code values program) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧ Ready program values work ∧ R work)
      (timeBound values program) := by
  rintro inp work out ⟨hc, hs, hb, hp, hr⟩
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdwork⟩ := run scratch program values before input emitted inp work out hc hs hb hv hp
  exact ⟨d, t, ht, hreach, hhalt, hdcur, by simpa only [hdwork] using hs,
    by simpa only [hdwork] using hb, by simpa only [hdwork] using hp, by simpa only [hdwork] using hr⟩

end JointThermoComplexity.Complexity.OutputProgram

#print axioms JointThermoComplexity.Complexity.OutputProgram.hoareTime
