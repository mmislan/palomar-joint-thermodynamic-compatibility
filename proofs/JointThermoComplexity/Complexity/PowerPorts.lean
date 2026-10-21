module
public import proofs.JointThermoComplexity.Complexity.GateStore

set_option autoImplicit false
@[expose] public section

/-! Fixed spare-register ports for a record-driven repeated-squaring block. -/

namespace JointThermoComplexity.Complexity.PowerPorts

def nextOld (m : ℕ) : Fin (m + 12) := ⟨2, by omega⟩
def scratchOld (m : ℕ) : Fin (m + 12) := ⟨5, by omega⟩
def next (m : ℕ) : Fin (m + 13) := (nextOld m).castSucc
def accumulator (m : ℕ) : Fin (m + 13) := ⟨3, by omega⟩
def power (m : ℕ) : Fin (m + 13) := ⟨4, by omega⟩
def scratch (m : ℕ) : Fin (m + 13) := (scratchOld m).castSucc
def base (m : ℕ) : Fin (m + 13) := ⟨6, by omega⟩

def accumulatorPermutation (m : ℕ) : Fin (m + 13) ≃ Fin (m + 13) :=
  Equiv.swap (Fin.last (m + 12)) (accumulator m)
def powerPermutation (m : ℕ) : Fin (m + 13) ≃ Fin (m + 13) :=
  Equiv.swap (Fin.last (m + 12)) (power m)

theorem next_ne_accumulator (m : ℕ) : next m ≠ accumulator m := by
  intro h; have hv := congrArg Fin.val h; change (2 : ℕ) = 3 at hv; omega
theorem next_ne_power (m : ℕ) : next m ≠ power m := by
  intro h; have hv := congrArg Fin.val h; change (2 : ℕ) = 4 at hv; omega
theorem next_ne_scratch (m : ℕ) : next m ≠ scratch m := by
  intro h; have hv := congrArg Fin.val h; change (2 : ℕ) = 5 at hv; omega
theorem accumulator_ne_power (m : ℕ) : accumulator m ≠ power m := by
  intro h; have hv := congrArg Fin.val h; change (3 : ℕ) = 4 at hv; omega
theorem accumulator_ne_scratch (m : ℕ) : accumulator m ≠ scratch m := by
  intro h; have hv := congrArg Fin.val h; change (3 : ℕ) = 5 at hv; omega
theorem power_ne_scratch (m : ℕ) : power m ≠ scratch m := by
  intro h; have hv := congrArg Fin.val h; change (4 : ℕ) = 5 at hv; omega

theorem next_ne_last (m : ℕ) : next m ≠ Fin.last (m + 12) := by
  intro h; have hv := congrArg Fin.val h; change (2 : ℕ) = m + 12 at hv; omega
theorem scratch_ne_last (m : ℕ) : scratch m ≠ Fin.last (m + 12) := by
  intro h; have hv := congrArg Fin.val h; change (5 : ℕ) = m + 12 at hv; omega

theorem accumulator_next (m : ℕ) : GateStore.next (accumulatorPermutation m) (nextOld m) = next m :=
  Equiv.swap_apply_of_ne_of_ne (next_ne_last m) (next_ne_accumulator m)
theorem power_next (m : ℕ) : GateStore.next (powerPermutation m) (nextOld m) = next m :=
  Equiv.swap_apply_of_ne_of_ne (next_ne_last m) (next_ne_power m)
theorem accumulator_scratch (m : ℕ) : GateStore.scratch (accumulatorPermutation m) (scratchOld m) = scratch m :=
  Equiv.swap_apply_of_ne_of_ne (scratch_ne_last m) (accumulator_ne_scratch m).symm
theorem power_scratch (m : ℕ) : GateStore.scratch (powerPermutation m) (scratchOld m) = scratch m :=
  Equiv.swap_apply_of_ne_of_ne (scratch_ne_last m) (power_ne_scratch m).symm
theorem accumulator_destination (m : ℕ) : CountSumAt.destination (accumulatorPermutation m) = accumulator m :=
  Equiv.swap_apply_left _ _
theorem power_destination (m : ℕ) : CountSumAt.destination (powerPermutation m) = power m :=
  Equiv.swap_apply_left _ _

end JointThermoComplexity.Complexity.PowerPorts

#print axioms JointThermoComplexity.Complexity.PowerPorts.power_next
