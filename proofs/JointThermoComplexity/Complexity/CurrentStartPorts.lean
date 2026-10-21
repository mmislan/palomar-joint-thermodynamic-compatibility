module
public import proofs.JointThermoComplexity.Complexity.CurrentPorts

set_option autoImplicit false
@[expose] public section

/-! Physical copies initialize the raw prefix tally and current cursor from retained input dimensions. -/

namespace JointThermoComplexity.Complexity.CurrentStartPorts

def offsetOld (m : ℕ) : Fin (m + 14) := ⟨0, by omega⟩

def currentPermutation (m : ℕ) : Fin (m + 15) ≃ Fin (m + 15) :=
  Equiv.swap (Fin.last (m + 14)) (MonomialPorts.species (m + 1))

theorem raw_source (m : ℕ) : (offsetOld m).castSucc = CountLayout.offset (m + 7) := rfl

theorem current_destination (m : ℕ) : CountSumAt.destination (currentPermutation m) = MonomialPorts.species (m + 1) :=
  Equiv.swap_apply_left _ _

theorem current_source (m : ℕ) :
    currentPermutation m (CurrentPorts.speciesOld m).castSucc = MonomialFuel.slot (m + 1) :=
  Equiv.swap_apply_of_ne_of_ne (CountOffset.cast_ne_destination (CurrentPorts.speciesOld m))
    (MonomialFuel.slot_separate (m + 1)).species

theorem current_zero (m : ℕ) :
    currentPermutation m (PowerPorts.scratchOld (m + 2)).castSucc = PowerPorts.scratch (m + 2) :=
  Equiv.swap_apply_of_ne_of_ne (PowerPorts.scratch_ne_last (m + 2)) (MonomialPorts.species_ne_scratch (m + 1)).symm

end JointThermoComplexity.Complexity.CurrentStartPorts

#print axioms JointThermoComplexity.Complexity.CurrentStartPorts.current_source
