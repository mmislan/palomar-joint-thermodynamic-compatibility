module
public import proofs.JointThermoComplexity.Complexity.OuterFuelPorts

set_option autoImplicit false
@[expose] public section

/-! Copy actual bounded species/core counts to separate fixed fuel tapes, preserving every other tape and output. -/

namespace JointThermoComplexity.Complexity.OuterFuelCopy
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt OuterFuelPorts

def machine (m : ℕ) (k : Fin 2) : TM (m + 22) := UnaryCopy.machine (permutation m k) (sourceOld m k) (zeroOld m)

theorem hoareTime (m : ℕ) (k : Fin 2) (old value : ℕ) (before remaining emitted : List Bool)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ destination m k → work' j = work j) → R work → R work') :
    (machine m k).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg old (work (destination m k)) ∧ IsReg value (work (source m k)) ∧
        BinaryIncrementRun.Register 0 (work (zero m)) ∧ R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg value (work (destination m k)) ∧ BinaryIncrementRun.Register 0 (work (zero m)) ∧ R work)
      (2 * old + 5 * value + 15) := by
  rintro inp work out ⟨hc, hs, hd, hsrc, hz, hr⟩
  let P : (Fin (m + 22) → Tape) → Prop := fun work' => ∀ j, j ≠ destination m k → work' j = work j
  have hP : ∀ work' work'',
      (∀ j, j ≠ CountSumAt.destination (permutation m k) → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj
    rw [destination_route] at hw
    exact (hw j hj).trans (hp j hj)
  have hzero : IsReg 0 (work (zero m)) :=
    CountTape.register_of_string (by simpa only [Nat.zero_bits, List.replicate_zero] using hz.1) hz.2
  have hcopy := UnaryCopy.hoareTime (permutation m k) (sourceOld m k) (zeroOld m) old value before remaining emitted P hP
  simp only [destination_route, source_route, zero_route] at hcopy
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hds, hdest, _, _, hw⟩ :=
    hcopy inp work out ⟨hc, hs, hd, hsrc, hzero, fun _ _ => rfl⟩
  exact ⟨d, t, ht, hreach, hhalt, hdc, hds, hdest,
    by simpa only [hw _ (zero_ne_destination m k)] using hz, hR work d.work hw hr⟩

end JointThermoComplexity.Complexity.OuterFuelCopy

#print axioms JointThermoComplexity.Complexity.OuterFuelCopy.hoareTime
