module
public import proofs.JointThermoComplexity.Complexity.StrictScheduleProgram
public import proofs.JointThermoComplexity.Complexity.SourceBinderBuffer
public import proofs.JointThermoComplexity.Complexity.CounterInputEntry

set_option autoImplicit false
@[expose] public section

/-! Blank-tape entry, measured input length, quiet unary header and all strict
schedule counts. The actual bound holds for every binary input word. -/

namespace JointThermoComplexity.Complexity.StrictScheduleEntry
open _root_.Complexity _root_.Complexity.TM
open DInstabilityComplexity.MachineConstruction
open HeaderAt (Cursor)
open BoxBufferState (Stored)

def ports : CounterProgramFrame.Ports 16 64 where
  index := ![30, 61, 31, 32, 60, 33, 34, 35, 36, 37, 38, 39, 40, 41, 24, 29]
  injective := by decide

theorem ports_ne_flag : ∀ i, ports.index i ≠ 62 := by decide
theorem ports_ne_sink : ∀ i, ports.index i ≠ 63 := by decide

def permutation : Fin 63 ≃ Fin 63 := Equiv.refl _
def header : TM 64 := SourceBinderBuffer.machine permutation
def measured (input : List Bool) : Fin 64 → Tape := BoundedCounters.inputWork 30 input

def Initial (input : List Bool) : _root_.Complexity.TM.TapePred 64 := fun inp work out =>
  inp = Tape.init (input.map Γ.ofBool) ∧ (∀ j, work j = Tape.init []) ∧ out = Tape.init []

def Preserved (input : List Bool) (work : Fin 64 → Tape) : Prop :=
  ∀ j, j ≠ 61 → j ≠ 62 → j ≠ 63 → work j = measured input j

theorem preserved_stable (input : List Bool) (work next : Fin 64 → Tape)
    (he : ∀ j, j ≠ SourceBinderBuffer.buffer 61 → j ≠ SourceBinderBuffer.counter permutation →
      j ≠ SourceBinderBuffer.flag permutation → next j = work j) :
    Preserved input work → Preserved input next := by
  intro h j h61 h62 h63
  exact (he j h63 h61 h62).trans (h j h61 h62 h63)

def HeaderPre (input : List Bool) : _root_.Complexity.TM.TapePred 64 := fun inp work out =>
  Cursor [] input [] inp work out ∧ (∀ j, Parked (work j)) ∧
    (work 63).HasBinaryPrefix [] ∧ (work 63).cells 0 = Γ.start ∧
    IsReg 0 (work 61) ∧ (work 62).head = 1 ∧ Preserved input work

theorem measured_register (input : List Bool) (j : Fin 64) :
    IsReg (if j = 30 then input.length else 0) (measured input j) := by
  by_cases hj : j = 30
  · subst j
    simpa only [measured, BoundedCounters.inputWork, Function.update_self, ↓reduceIte] using reg_regT input.length
  · simpa only [measured, BoundedCounters.inputWork, Function.update_of_ne hj, ite_eq_right hj] using reg_regT 0

theorem entry_hoareTime (input : List Bool) :
    (BoundedCounters.entry (30 : Fin 64)).HoareTime (Initial input) (HeaderPre input)
      (2 * input.length + 6) := by
  have h := BoundedCounters.entry_hoareTime (30 : Fin 64) input
  rw [BoundedCounters.inputWork_eq] at h
  apply h.strengthen_post
  rintro inp work out ⟨hi, hw, ho⟩
  have hsafe : ∀ j, Parked (work j) := by
    intro j
    rw [hw]
    exact (measured_register input j).parked
  have hreg : ∀ j, IsReg (if j = 30 then input.length else 0) (work j) := by
    intro j
    rw [hw]
    exact measured_register input j
  have hz : IsReg 0 (work 63) := by simpa only [Fin.reduceEq, ite_false] using hreg 63
  have hc : Cursor [] input [] inp work out := by
    refine ⟨by rw [hi]; rfl, by rw [hi]; rfl,
      (fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩), ?_, ho.2.1⟩
    exact ⟨ho.1, ho.2.2.1, fun i _ => ho.2.2.2 (i + 1) (by simp)⟩
  exact ⟨hc, hsafe, CountTape.empty_prefix_of_zero hz, hz.cell0,
    by simpa only [Fin.reduceEq, ite_false] using hreg 61,
    (hreg 62).head_eq, fun j _ _ _ => congrFun hw j⟩

def Frame (input : List Bool) (work : Fin 64 → Tape) : Prop :=
  (work 62).head = 1 ∧ (work 62).read = Γ.ofBool (HeaderControl.valid input) ∧
    Stored (HeaderControl.copied input) (work 63) ∧
    ∀ j, (∀ i, j ≠ ports.index i) → j ≠ 62 → j ≠ 63 → IsReg 0 (work j)

theorem frame_stable (input : List Bool) : CounterProgramFrame.Stable ports (Frame input) := by
  rintro work next he ⟨hh, hf, hb, hz⟩
  have h62 : next 62 = work 62 := he 62 (fun i => (ports_ne_flag i).symm)
  have h63 : next 63 = work 63 := he 63 (fun i => (ports_ne_sink i).symm)
  exact ⟨by simpa only [h62] using hh, by simpa only [h62] using hf,
    by simpa only [h63] using hb,
    fun j hj hflag hsink => by simpa only [he j hj] using hz j hj hflag hsink⟩

theorem header_hoareTime (input : List Bool) :
    header.HoareTime (HeaderPre input)
      (CounterProgramFrame.Logical ports (StrictScheduleProgram.initialValues input.length (HeaderControl.count input))
        (HeaderControl.copied input) (HeaderControl.suffix input) [] (Frame input))
      (2 * HeaderControl.count input + 5) := by
  have h := SourceBinderBuffer.hoareTime permutation [] input [] (Preserved input) (preserved_stable input)
  apply h.strengthen_post
  rintro inp work out ⟨hc, hs, hb, hn, hfh, hfr, he⟩
  have hc' : Cursor (HeaderControl.copied input) (HeaderControl.suffix input) [] inp work out := by
    simpa only [List.nil_append] using hc
  have hregs : ∀ i, IsReg (StrictScheduleProgram.initialValues input.length (HeaderControl.count input) i)
      (work (ports.index i)) := by
    intro i
    by_cases hi1 : i = 1
    · subst i
      exact hn
    · have hne61 : ports.index i ≠ 61 := ports.injective.ne hi1
      rw [he (ports.index i) hne61 (ports_ne_flag i) (ports_ne_sink i)]
      have hv := measured_register input (ports.index i)
      by_cases hi0 : i = 0
      · subst i
        exact hv
      · have hne30 : ports.index i ≠ 30 := ports.injective.ne hi0
        simpa only [StrictScheduleProgram.initialValues, ite_eq_right hi0, ite_eq_right hi1, ite_eq_right hne30] using hv
  have hzero : ∀ j, (∀ i, j ≠ ports.index i) → j ≠ 62 → j ≠ 63 → IsReg 0 (work j) := by
    intro j hj hf hb
    rw [he j (hj 1) hf hb]
    have hj30 : j ≠ (30 : Fin 64) := hj 0
    simpa only [ite_eq_right hj30] using measured_register input j
  exact ⟨hc', hs, hregs, hfh, hfr, hb, hzero⟩

def machine : TM 64 :=
  seqTM (seqTM (BoundedCounters.entry 30) header) (StrictScheduleProgram.machine ports)

def timeBound (L : ℕ) : ℕ := 4 * L + 13 + counterIterTime StrictScheduleProgram.program.length L

noncomputable def timePolynomial : Polynomial ℕ :=
  4 * Polynomial.X + 13 + counterTimePolynomial StrictScheduleProgram.program.length

theorem timePolynomial_eval (L : ℕ) : timePolynomial.eval L = timeBound L := by
  simp [timePolynomial, timeBound, counterTimePolynomial_eval]

theorem hoareTime (input : List Bool) :
    machine.HoareTime (Initial input)
      (CounterProgramFrame.Logical ports
        (StrictScheduleProgram.values input.length (HeaderControl.count input)
          (counterProgramEval StrictScheduleProgram.core
            (StrictScheduleProgram.initialValues input.length (HeaderControl.count input)) 4))
        (HeaderControl.copied input) (HeaderControl.suffix input) [] (Frame input))
      (timeBound input.length) := by
  have he := entry_hoareTime input
  have hh := header_hoareTime input
  have hfirst := seqTM_hoareTime _ _ he (by
    rintro inp work out ⟨hc, hs, hb, hz, hn, hf, hp⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hb, hz, hn, hf, hp⟩) hh
  have hs := StrictScheduleProgram.hoareTime ports input.length (HeaderControl.count input)
    (HeaderControl.count_le_length input) (HeaderControl.copied input) (HeaderControl.suffix input) []
    (Frame input) (frame_stable input)
  have hall := seqTM_hoareTime _ _ hfirst (by
    rintro inp work out ⟨hc, hs, hv, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hv, hx⟩) hs
  apply hall.mono_bound
  have hc := HeaderControl.count_le_length input
  unfold timeBound
  omega

end JointThermoComplexity.Complexity.StrictScheduleEntry

#print axioms JointThermoComplexity.Complexity.StrictScheduleEntry.entry_hoareTime
#print axioms JointThermoComplexity.Complexity.StrictScheduleEntry.header_hoareTime
#print axioms JointThermoComplexity.Complexity.StrictScheduleEntry.timePolynomial_eval
#print axioms JointThermoComplexity.Complexity.StrictScheduleEntry.hoareTime
