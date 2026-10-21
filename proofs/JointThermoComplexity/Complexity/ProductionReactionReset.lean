module
public import proofs.JointThermoComplexity.Complexity.ProductionInitialState

set_option autoImplicit false
@[expose] public section

/-! Reset the bounded actual reaction position, retaining reusable arithmetic state and every other tape. -/

namespace JointThermoComplexity.Complexity.ProductionReactionReset
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts

theorem hoareTime (m L n old si : ℕ) (before remaining emitted : List Bool)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ reaction m → work' j = work j) → R work → R work') :
    (clearWorkTM (reaction m)).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.State m L n old si work ∧ R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ ProductionOperandLoad.State m L n 0 si work ∧ R work)
      (2 * old + 5) := by
  rintro inp work out ⟨hc, hp, hr⟩
  let P : (Fin (m + 20) → Tape) → Prop := fun work' => ∀ j, j ≠ reaction m → work' j = work j
  have hP : ∀ work' work'', (∀ j, j ≠ reaction m → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj
    exact (hw j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hd, hh, hc', hs, hz, hw⟩ := UnaryReset.hoareTime (reaction m) old before remaining emitted P hP
    inp work out ⟨hc, hp.safe, hp.reactionPosition, fun _ _ => rfl⟩
  have hx (j : Fin (m + 20)) (hj : j.val ≠ 6) : d.work j = work j := by
    apply hw j
    intro he
    exact hj (congrArg Fin.val he)
  have hstate : ProductionOperandLoad.State m L n 0 si d.work :=
    ⟨hs, by simpa only [hx (left m) (by change (9 : ℕ) ≠ 6; omega)] using hp.productReusable,
      by simpa only [hx (right m) (by change (10 : ℕ) ≠ 6; omega)] using hp.reactantReusable,
      by simpa only [hx (magnitude m) (by change (8 : ℕ) ≠ 6; omega)] using hp.magnitudeReusable,
      by simpa only [hx (sign m) (by change (11 : ℕ) ≠ 6; omega)] using hp.signHead,
      by simpa only [hx (species m) (by change (12 : ℕ) ≠ 6; omega)] using hp.speciesPosition,
      by simpa only [hx (count m) (by change m + 15 ≠ 6; omega)] using hp.speciesCount, hz⟩
  exact ⟨d, t, ht, hd, hh, hc', hstate, hR work d.work hw hr⟩

end JointThermoComplexity.Complexity.ProductionReactionReset

#print axioms JointThermoComplexity.Complexity.ProductionReactionReset.hoareTime
