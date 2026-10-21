module
public import proofs.JointThermoComplexity.Complexity.ReactionFuel

set_option autoImplicit false
@[expose] public section

/-! The current-equation rescan reuses the old gate tally, prior result and source-index working ports. -/

namespace JointThermoComplexity.Complexity.CurrentPorts

def raw (m : ℕ) : Fin (m + 15) := CountAppend.destination
def speciesOld (m : ℕ) : Fin (m + 14) := ⟨m + 10, by omega⟩
def copySourceOld (m : ℕ) : Fin (m + 14) := ⟨6, by omega⟩

theorem raw_layout (m : ℕ) : raw m = CountLayout.raw (m + 7) := rfl
theorem species_fuel (m : ℕ) : (speciesOld m).castSucc = MonomialFuel.slot (m + 1) := rfl

theorem copy_source (m : ℕ) :
    MonomialPorts.resultPermutation (m + 1) (copySourceOld m).castSucc = raw m :=
  Equiv.swap_apply_right _ _

theorem raw_ne_previous (m : ℕ) : raw m ≠ MonomialPorts.previous (m + 1) :=
  (MonomialPorts.previous_ne_last (m + 1)).symm

theorem raw_ne_scratch (m : ℕ) : raw m ≠ PowerPorts.scratch (m + 2) :=
  (PowerPorts.scratch_ne_last (m + 2)).symm

theorem raw_ne_current (m : ℕ) : raw m ≠ MonomialPorts.species (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change m + 14 = 7 at hv; omega

theorem raw_ne_speciesFuel (m : ℕ) : raw m ≠ MonomialFuel.slot (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change m + 14 = m + 1 + 9 at hv; omega

theorem raw_ne_reactionFuel (m : ℕ) : raw m ≠ ReactionFuel.slot m := by
  intro h; have hv := congrArg Fin.val h; change m + 14 = m + 11 at hv; omega

end JointThermoComplexity.Complexity.CurrentPorts

#print axioms JointThermoComplexity.Complexity.CurrentPorts.copy_source
