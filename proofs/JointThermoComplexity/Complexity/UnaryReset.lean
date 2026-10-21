module
public import proofs.JointThermoComplexity.Complexity.BinaryClear
public import proofs.JointThermoComplexity.Complexity.SafeExecution
public import proofs.JointThermoComplexity.Complexity.CountTape

set_option autoImplicit false
@[expose] public section

/-! Reset a bounded canonical address register, preserving the surrounding cursor and work frame. -/

namespace JointThermoComplexity.Complexity.UnaryReset
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

theorem hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (clearWorkTM idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg v (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg 0 (work idx) ∧ R work)
      (2 * v + 5) := by
  have hc := BinaryClear.hoareTime idx (List.replicate v true) before input emitted R hR
  have hsafe := SafeExecution.hoareTime (clearWorkTM idx) _ _ _ hc (by
    rintro inp work out ⟨hcur, _, _⟩ j
    exact (hcur.works j).2)
  exact hsafe.consequence
    (fun _ _ _ ⟨hcur, hs, hv, hr⟩ => ⟨⟨hcur, CountTape.string_of_register hv, hv.cell0, hr⟩, hs⟩)
    (fun _ _ _ ⟨⟨hcur, hv, hr⟩, hs⟩ => ⟨hcur, hs,
      CountTape.register_of_string (by simpa only [List.replicate_zero, Nat.zero_bits] using hv.1) hv.2, hr⟩)
    (by simp only [List.length_replicate]; omega)

end JointThermoComplexity.Complexity.UnaryReset

#print axioms JointThermoComplexity.Complexity.UnaryReset.hoareTime
