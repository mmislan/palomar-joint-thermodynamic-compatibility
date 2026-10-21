module
public import proofs.JointThermoComplexity.Complexity.ReactionPorts

set_option autoImplicit false
@[expose] public section

/-! Copy the retained activity/current offset into the next gate address. -/

namespace JointThermoComplexity.Complexity.NetworkSeedPorts

def sourceOld (m : ℕ) : Fin (m + 14) := ⟨0, by omega⟩

def permutation (m : ℕ) : Fin (m + 15) ≃ Fin (m + 15) :=
  Equiv.swap (Fin.last (m + 14)) (PowerPorts.next (m + 2))

theorem destination (m : ℕ) : CountSumAt.destination (permutation m) = PowerPorts.next (m + 2) :=
  Equiv.swap_apply_left _ _

theorem source (m : ℕ) : permutation m (sourceOld m).castSucc = CountLayout.offset (m + 7) := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h; have hv := congrArg Fin.val h; change (0 : ℕ) = m + 14 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change (0 : ℕ) = 2 at hv; omega

theorem zero (m : ℕ) :
    permutation m (PowerPorts.scratchOld (m + 2)).castSucc = PowerPorts.scratch (m + 2) :=
  Equiv.swap_apply_of_ne_of_ne (PowerPorts.scratch_ne_last (m + 2)) (PowerPorts.next_ne_scratch (m + 2)).symm

end JointThermoComplexity.Complexity.NetworkSeedPorts

#print axioms JointThermoComplexity.Complexity.NetworkSeedPorts.source
