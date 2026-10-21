module
public import proofs.JointThermoComplexity.Complexity.CounterInputEntry
public import proofs.JointThermoComplexity.Complexity.BinaryConstantAdd
public import proofs.JointThermoComplexity.Complexity.SparseOffsetPorts
public import proofs.JointThermoComplexity.Complexity.SourceTermToken
public import proofs.JointThermoComplexity.Complexity.VirtualCursor

set_option autoImplicit false
@[expose] public section

/-! Measure input length and initialize the counted pass from blank tapes. -/

namespace JointThermoComplexity.Complexity.SparseInputInitialization
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open SparseOffsetPorts

def Stable (R : (Fin 33 → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ layout.acc.castSucc → j ≠ marker.castSucc → next j = work j) → R work → R next

def prepare : TM 33 := seqTM (BinaryConstantAdd.machine 1 layout.acc.castSucc) (SourceTermToken.setStatus marker.castSucc true)

def machine : TM 33 := seqTM (BoundedCounters.entry fuel.castSucc) prepare

def Initial (input : List Bool) : _root_.Complexity.TM.TapePred 33 := fun inp work out =>
  inp = Tape.init (input.map Γ.ofBool) ∧ (∀ j, work j = Tape.init []) ∧ out = Tape.init []

def Ready (L : ℕ) (input : List Bool) : _root_.Complexity.TM.TapePred 33 := fun inp work out =>
  Cursor [] input [] inp work out ∧ (∀ j, Parked (work j)) ∧ (∀ j, (work j).cells 0 = Γ.start) ∧
    Register 1 (work layout.acc.castSucc) ∧ (work marker.castSucc).head = 1 ∧
      (work marker.castSucc).read = Γ.one ∧ IsReg L (work fuel.castSucc) ∧
        ∀ j, j ≠ layout.acc.castSucc → j ≠ marker.castSucc → j ≠ fuel.castSucc → IsReg 0 (work j)

theorem binary_zero {t : Tape} (h : IsReg 0 t) : Register 0 t :=
  ⟨by simpa only [Nat.zero_bits, List.replicate_zero] using CountTape.string_of_register h, h.cell0⟩

theorem prepare_hoareTime (before input emitted : List Bool) (R : (Fin 33 → Tape) → Prop) (hR : Stable R) :
    prepare.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ j, (work j).cells 0 = Γ.start) ∧ Register 0 (work layout.acc.castSucc) ∧
          (work marker.castSucc).head = 1 ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (∀ j, (work j).cells 0 = Γ.start) ∧ Register 1 (work layout.acc.castSucc) ∧
          (work marker.castSucc).head = 1 ∧ (work marker.castSucc).read = Γ.one ∧ R work) 9 := by
  let S : (Fin 33 → Tape) → Prop := fun work => (work marker.castSucc).head = 1 ∧ R work
  have hS : BinaryIncrementFramed.Stable layout.acc.castSucc S := by
    rintro work next he ⟨hh, hr⟩
    exact ⟨by rw [he marker.castSucc (by decide)]; exact hh,
      hR work next (fun j hj _ => he j hj) hr⟩
  let T : (Fin 33 → Tape) → Prop := fun work => Register 1 (work layout.acc.castSucc) ∧ R work
  have hT : ∀ work next, (∀ j, j ≠ marker.castSucc → next j = work j) → T work → T next := by
    rintro work next he ⟨ha, hr⟩
    exact ⟨by rw [he layout.acc.castSucc (by decide)]; exact ha,
      hR work next (fun j _ hj => he j hj) hr⟩
  have ha := BinaryConstantAdd.hoareTime 1 layout.acc.castSucc 0 before input emitted S hS
  have hm := SourceTermToken.setStatus_hoareTime marker.castSucc true before input emitted T hT
  have hall := seqTM_hoareTime _ _ ha (by
    rintro inp work out ⟨hc, hs, hv, hh, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hh, hv, hr⟩) hm
  rintro inp work out ⟨hc, hs, hz, ha, hh, hr⟩
  obtain ⟨d, t, ht, hd, hhalt, hc', hs', hh', hv', ha', hr'⟩ := hall inp work out ⟨hc, hs, ha, hh, hr⟩
  have hz' := VirtualCursor.markers_reaches prepare hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hz j, (hs j).2⟩) (VirtualCursor.output_safe hc)
  exact ⟨d, t, by simpa only [Nat.zero_bits, List.length_nil] using ht, hd, hhalt,
    hc', hs', fun j => (hz'.2.1 j).1, ha', hh', hv', hr'⟩

theorem hoareTime (input : List Bool) :
    machine.HoareTime (Initial input) (Ready input.length input) (2 * input.length + 16) := by
  let W := BoundedCounters.inputWork fuel.castSucc input
  have hreg (j : Fin 33) : IsReg (if j = fuel.castSucc then input.length else 0) (W j) := by
    by_cases hj : j = fuel.castSucc
    · subst j
      simpa only [W, BoundedCounters.inputWork, Function.update_self, ↓reduceIte] using reg_regT input.length
    · simpa only [W, BoundedCounters.inputWork, Function.update_of_ne hj, hj, ↓reduceIte] using reg_regT 0
  have hsafe (j : Fin 33) : Parked (W j) := (hreg j).parked
  let R : (Fin 33 → Tape) → Prop := fun work => IsReg input.length (work fuel.castSucc) ∧
    ∀ j, j ≠ layout.acc.castSucc → j ≠ marker.castSucc → j ≠ fuel.castSucc → IsReg 0 (work j)
  have hR : Stable R := by
    rintro work next he ⟨hf, hr⟩
    exact ⟨by rw [he fuel.castSucc (by decide) (by decide)]; exact hf,
      fun j ha hm hf => by rw [he j ha hm]; exact hr j ha hm hf⟩
  have he := BoundedCounters.entry_hoareTime fuel.castSucc input
  rw [BoundedCounters.inputWork_eq] at he
  have hp := prepare_hoareTime [] input [] R hR
  have hs := seqTM_hoareTime _ _ he (by
    rintro inp work out ⟨hi, hw, ho⟩
    have hout := (FixedOutput.outAcc_iff _ _).mp ho
    have hcur : Cursor [] input [] inp work out := by
      refine ⟨?_, ?_, ?_, hout.1, hout.2⟩
      · rw [hi]; rfl
      · rw [hi]; rfl
      · intro j
        rw [hw]
        exact ⟨(hsafe j).read_ne_start, (hsafe j).1⟩
    obtain ⟨hin, hwork, hout⟩ := hcur.phase
    rw [hin, hwork, hout]
    refine ⟨hcur, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j; rw [hw]; exact hsafe j
    · intro j; rw [hw]; exact (hreg j).cell0
    · rw [hw]
      apply binary_zero
      simpa only [show layout.acc.castSucc ≠ fuel.castSucc from by decide, ↓reduceIte] using hreg layout.acc.castSucc
    · rw [hw]; exact (hreg marker.castSucc).head_eq
    · rw [hw]; simpa only [↓reduceIte] using hreg fuel.castSucc
    · intro j _ _ hj
      rw [hw]
      simpa only [hj, ↓reduceIte] using hreg j) hp
  exact hs.mono_bound (by omega)

end JointThermoComplexity.Complexity.SparseInputInitialization

#print axioms JointThermoComplexity.Complexity.SparseInputInitialization.prepare_hoareTime
#print axioms JointThermoComplexity.Complexity.SparseInputInitialization.hoareTime
