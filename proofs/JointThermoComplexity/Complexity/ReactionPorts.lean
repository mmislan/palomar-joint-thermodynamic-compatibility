module
public import proofs.JointThermoComplexity.Complexity.MonomialFuel

set_option autoImplicit false
@[expose] public section

/-! A spare address register preserves the first monomial while the second is computed. -/

namespace JointThermoComplexity.Complexity.ReactionPorts

def saved (m : ℕ) : Fin (m + 15) := ⟨8, by omega⟩
def copyPreviousOld (m : ℕ) : Fin (m + 14) := ⟨6, by omega⟩
def copyZeroOld (m : ℕ) : Fin (m + 14) := PowerPorts.scratchOld (m + 2)

theorem saved_ne_next (m : ℕ) : saved m ≠ PowerPorts.next (m + 2) := by
  intro h; have hv := congrArg Fin.val h; change (8 : ℕ) = 2 at hv; omega
theorem saved_ne_accumulator (m : ℕ) : saved m ≠ PowerPorts.accumulator (m + 2) := by
  intro h; have hv := congrArg Fin.val h; change (8 : ℕ) = 3 at hv; omega
theorem saved_ne_power (m : ℕ) : saved m ≠ PowerPorts.power (m + 2) := by
  intro h; have hv := congrArg Fin.val h; change (8 : ℕ) = 4 at hv; omega
theorem saved_ne_scratch (m : ℕ) : saved m ≠ PowerPorts.scratch (m + 2) := by
  intro h; have hv := congrArg Fin.val h; change (8 : ℕ) = 5 at hv; omega
theorem saved_ne_previous (m : ℕ) : saved m ≠ MonomialPorts.previous (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (8 : ℕ) = 6 at hv; omega
theorem saved_ne_species (m : ℕ) : saved m ≠ MonomialPorts.species (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (8 : ℕ) = 7 at hv; omega
theorem saved_ne_flag (m : ℕ) : saved m ≠ PowerBitState.flag (m + 2) := by
  intro h; have hv := congrArg Fin.val h; change (8 : ℕ) = m + 2 + 11 at hv; omega
theorem saved_ne_fuel (m : ℕ) : saved m ≠ MonomialFuel.slot (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (8 : ℕ) = m + 1 + 9 at hv; omega
theorem saved_ne_last (m : ℕ) : saved m ≠ Fin.last (m + 14) := by
  intro h; have hv := congrArg Fin.val h; change (8 : ℕ) = m + 14 at hv; omega

def savedPermutation (m : ℕ) : Fin (m + 15) ≃ Fin (m + 15) :=
  Equiv.swap (Fin.last (m + 14)) (saved m)

theorem saved_destination (m : ℕ) : CountSumAt.destination (savedPermutation m) = saved m :=
  Equiv.swap_apply_left _ _

theorem copy_previous (m : ℕ) :
    savedPermutation m (copyPreviousOld m).castSucc = MonomialPorts.previous (m + 1) := by
  change savedPermutation m (MonomialPorts.previous (m + 1)) = _
  exact Equiv.swap_apply_of_ne_of_ne (MonomialPorts.previous_ne_last (m + 1)) (saved_ne_previous m).symm

theorem copy_zero (m : ℕ) :
    savedPermutation m (copyZeroOld m).castSucc = PowerPorts.scratch (m + 2) := by
  change savedPermutation m (PowerPorts.scratch (m + 2)) = _
  exact Equiv.swap_apply_of_ne_of_ne (PowerPorts.scratch_ne_last (m + 2)) (saved_ne_scratch m).symm

theorem saved_next (m : ℕ) :
    GateStore.next (savedPermutation m) (PowerPorts.nextOld (m + 2)) = PowerPorts.next (m + 2) :=
  Equiv.swap_apply_of_ne_of_ne (PowerPorts.next_ne_last (m + 2)) (saved_ne_next m).symm

theorem saved_scratch (m : ℕ) :
    GateStore.scratch (savedPermutation m) (PowerPorts.scratchOld (m + 2)) = PowerPorts.scratch (m + 2) := copy_zero m

end JointThermoComplexity.Complexity.ReactionPorts

#print axioms JointThermoComplexity.Complexity.ReactionPorts.copy_previous
