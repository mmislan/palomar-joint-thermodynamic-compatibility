module
public import proofs.JointThermoComplexity.Complexity.ProductionInitialState

set_option autoImplicit false
@[expose] public section

/-! Initialize the actual shared-current address from the retained species count, without compiling input values into control. -/

namespace JointThermoComplexity.Complexity.ProductionCurrentReset
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts

theorem hoareTime (m L n ri si idx : ℕ) (before remaining emitted : List Bool)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ current m → work' j = work j) → R work → R work') :
    (CurrentStart.cursorMachine (m + 5)).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.State m L n ri si work ∧
        IsReg idx (work (current m)) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.State m L n ri si work ∧
        IsReg n (work (current m)) ∧ BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧ R work)
      (2 * idx + 5 * n + 15) := by
  rintro inp work out ⟨hc, hp, hi, hz, hr⟩
  let P : (Fin (m + 20) → Tape) → Prop := fun work' => ∀ j, j ≠ current m → work' j = work j
  have hP : ∀ work' work'',
      (∀ j, j ≠ CountSumAt.destination (CurrentStartPorts.currentPermutation (m + 5)) → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj
    rw [CurrentStartPorts.current_destination] at hw
    exact (hw j hj).trans (hp j hj)
  have hzero : IsReg 0 (work (PowerPorts.scratch (m + 7))) :=
    CountTape.register_of_string (by simpa only [Nat.zero_bits, List.replicate_zero] using hz.1) hz.2
  have hcopy := UnaryCopy.hoareTime (CurrentStartPorts.currentPermutation (m + 5)) (CurrentPorts.speciesOld (m + 5))
    (PowerPorts.scratchOld (m + 7)) idx n before remaining emitted P hP
  simp only [CurrentStartPorts.current_destination, CurrentStartPorts.current_source, CurrentStartPorts.current_zero] at hcopy
  obtain ⟨d, t, ht, hd, hh, hc', hs, hn, _, _, hw⟩ := hcopy inp work out
    ⟨hc, hp.safe, hi, hp.speciesCount, hzero, fun _ _ => rfl⟩
  have hx (j : Fin (m + 20)) (hj : j.val ≠ 7) : d.work j = work j := by
    apply hw j
    intro he
    exact hj (congrArg Fin.val he)
  have hstate : ProductionOperandLoad.State m L n ri si d.work :=
    ⟨hs, by simpa only [hx (left m) (by change (9 : ℕ) ≠ 7; omega)] using hp.productReusable,
      by simpa only [hx (right m) (by change (10 : ℕ) ≠ 7; omega)] using hp.reactantReusable,
      by simpa only [hx (magnitude m) (by change (8 : ℕ) ≠ 7; omega)] using hp.magnitudeReusable,
      by simpa only [hx (sign m) (by change (11 : ℕ) ≠ 7; omega)] using hp.signHead,
      by simpa only [hx (species m) (by change (12 : ℕ) ≠ 7; omega)] using hp.speciesPosition,
      by simpa only [hx (count m) (by change m + 15 ≠ 7; omega)] using hp.speciesCount,
      by simpa only [hx (reaction m) (by change (6 : ℕ) ≠ 7; omega)] using hp.reactionPosition⟩
  exact ⟨d, t, ht, hd, hh, hc', hstate, hn,
    by simpa only [hx (PowerPorts.scratch (m + 7)) (by change (5 : ℕ) ≠ 7; omega)] using hz, hR work d.work hw hr⟩

end JointThermoComplexity.Complexity.ProductionCurrentReset

#print axioms JointThermoComplexity.Complexity.ProductionCurrentReset.hoareTime
