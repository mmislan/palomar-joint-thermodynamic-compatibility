module
public import proofs.JointThermoComplexity.Complexity.CurrentPorts
public import proofs.JointThermoComplexity.Complexity.CopyPredecessor

set_option autoImplicit false
@[expose] public section

/-! Store the last reaction output address from the positive prefix next-address tally. -/

namespace JointThermoComplexity.Complexity.CurrentAddress
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts

def machine (m : ℕ) : TM (m + 15) :=
  CopyPredecessor.machine (resultPermutation (m + 1)) (copySourceOld m) (scratchOld (m + 2))

theorem hoareTime (m L old v : ℕ) (hold : old ≤ 4 * L) (hv : v + 1 ≤ 4 * L)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ previous (m + 1) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧ IsReg (v + 1) (work (raw m)) ∧
        IsReg old (work (previous (m + 1))) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧ IsReg (v + 1) (work (raw m)) ∧
        IsReg v (work (previous (m + 1))) ∧ R work) (36 * L + 33) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work => BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ CountSumAt.destination (resultPermutation (m + 1)) → work' j = work j) →
      P work → P work' := by
    rintro work work' hw ⟨hz, hr⟩
    rw [result_destination] at hw
    exact ⟨by simpa only [hw _ (previous_ne_scratch (m + 1)).symm] using hz, hR work work' hw hr⟩
  have hc := CopyPredecessor.hoareTime (resultPermutation (m + 1)) (copySourceOld m) (scratchOld (m + 2))
    old v before input emitted P hP
  simp only [result_destination, copy_source, show resultPermutation (m + 1) (scratchOld (m + 2)).castSucc =
    scratch (m + 2) from result_scratch (m + 1)] at hc
  exact hc.consequence (by
    rintro inp work out ⟨hcur, hs, hz, hn, hp, hr⟩
    exact ⟨hcur, hs, hp, hn,
      CountTape.register_of_string (by simpa only [Nat.zero_bits, List.replicate_zero] using hz.1) hz.2, hz, hr⟩)
    (fun _ _ _ ⟨hcur, hs, hp, hn, _, hz, hr⟩ => ⟨hcur, hs, hz, hn, hp, hr⟩) (by omega)

end JointThermoComplexity.Complexity.CurrentAddress

#print axioms JointThermoComplexity.Complexity.CurrentAddress.hoareTime
