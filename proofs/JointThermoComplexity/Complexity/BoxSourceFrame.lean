module
public import proofs.JointThermoComplexity.Complexity.BoxState

set_option autoImplicit false
@[expose] public section

/-! Preserve binary buffers and zero scratch when resetting or advancing only the source index. -/

namespace JointThermoComplexity.Complexity.BoxSourceFrame
open _root_.Complexity
open _root_.Complexity.TM
open PowerPorts MonomialPorts ReactionPorts BoxState

def Fixed (m L : ℕ) (R : (Fin (m + 15) → Tape) → Prop) (work : Fin (m + 15) → Tape) : Prop :=
  BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧ Buffers m L work ∧ R work

theorem frame (m L : ℕ) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → Fixed m L R work → Fixed m L R work' := by
  rintro work work' hw ⟨hz, ⟨hln, hld, hhn, hhd⟩, hr⟩
  have hsave : saved m ≠ species (m + 1) := by
    intro h; have hv := congrArg Fin.val h; change (8 : ℕ) = 7 at hv; omega
  exact ⟨by simpa only [hw _ (species_ne_scratch (m + 1)).symm] using hz,
    ⟨by simpa only [hw _ (species_ne_next (m + 1)).symm] using hln,
      by simpa only [hw _ (species_ne_accumulator (m + 1)).symm] using hld,
      by simpa only [hw _ (species_ne_power (m + 1)).symm] using hhn,
      by simpa only [hw _ hsave] using hhd⟩,
    hR work work' (fun j _ _ _ _ hj => hw j hj) hr⟩

end JointThermoComplexity.Complexity.BoxSourceFrame

#print axioms JointThermoComplexity.Complexity.BoxSourceFrame.frame
