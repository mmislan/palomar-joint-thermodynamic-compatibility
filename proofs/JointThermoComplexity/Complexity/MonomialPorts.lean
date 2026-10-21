module
public import proofs.JointThermoComplexity.Complexity.PowerBitState

set_option autoImplicit false
@[expose] public section

/-! One additional spare carries the current species address; the prior monomial uses port six. -/

namespace JointThermoComplexity.Complexity.MonomialPorts

def species (m : ℕ) : Fin (m + 14) := ⟨7, by omega⟩
def previous (m : ℕ) : Fin (m + 14) := PowerPorts.base (m + 1)

theorem species_ne_next (m : ℕ) : species m ≠ PowerPorts.next (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (7 : ℕ) = 2 at hv; omega
theorem species_ne_accumulator (m : ℕ) : species m ≠ PowerPorts.accumulator (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (7 : ℕ) = 3 at hv; omega
theorem species_ne_power (m : ℕ) : species m ≠ PowerPorts.power (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (7 : ℕ) = 4 at hv; omega
theorem species_ne_scratch (m : ℕ) : species m ≠ PowerPorts.scratch (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (7 : ℕ) = 5 at hv; omega
theorem species_ne_flag (m : ℕ) : species m ≠ PowerBitState.flag (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (7 : ℕ) = m + 1 + 11 at hv; omega
theorem previous_ne_next (m : ℕ) : previous m ≠ PowerPorts.next (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (6 : ℕ) = 2 at hv; omega
theorem previous_ne_accumulator (m : ℕ) : previous m ≠ PowerPorts.accumulator (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (6 : ℕ) = 3 at hv; omega
theorem previous_ne_power (m : ℕ) : previous m ≠ PowerPorts.power (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (6 : ℕ) = 4 at hv; omega
theorem previous_ne_scratch (m : ℕ) : previous m ≠ PowerPorts.scratch (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (6 : ℕ) = 5 at hv; omega
theorem previous_ne_species (m : ℕ) : previous m ≠ species m := by
  intro h; have hv := congrArg Fin.val h; change (6 : ℕ) = 7 at hv; omega
theorem previous_ne_flag (m : ℕ) : previous m ≠ PowerBitState.flag (m + 1) := by
  intro h; have hv := congrArg Fin.val h; change (6 : ℕ) = m + 1 + 11 at hv; omega
theorem previous_ne_last (m : ℕ) : previous m ≠ Fin.last (m + 13) := by
  intro h; have hv := congrArg Fin.val h; change (6 : ℕ) = m + 13 at hv; omega

def resultPermutation (m : ℕ) : Fin (m + 14) ≃ Fin (m + 14) :=
  Equiv.swap (Fin.last (m + 13)) (previous m)

theorem result_next (m : ℕ) :
    GateStore.next (resultPermutation m) (PowerPorts.nextOld (m + 1)) = PowerPorts.next (m + 1) :=
  Equiv.swap_apply_of_ne_of_ne (PowerPorts.next_ne_last (m + 1)) (previous_ne_next m).symm
theorem result_scratch (m : ℕ) :
    GateStore.scratch (resultPermutation m) (PowerPorts.scratchOld (m + 1)) = PowerPorts.scratch (m + 1) :=
  Equiv.swap_apply_of_ne_of_ne (PowerPorts.scratch_ne_last (m + 1)) (previous_ne_scratch m).symm
theorem result_destination (m : ℕ) : CountSumAt.destination (resultPermutation m) = previous m :=
  Equiv.swap_apply_left _ _

end JointThermoComplexity.Complexity.MonomialPorts

#print axioms JointThermoComplexity.Complexity.MonomialPorts.result_next
