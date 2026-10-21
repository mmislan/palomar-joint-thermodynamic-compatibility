module
public import proofs.JointThermoComplexity.Complexity.MonomialPorts
public import proofs.JointThermoComplexity.Complexity.CountLayout

set_option autoImplicit false
@[expose] public section

/-! The retained species-count register is separate from every monomial work port. -/

namespace JointThermoComplexity.Complexity.MonomialFuel
open PowerPorts MonomialPorts

structure Separate (m : ℕ) (r : Fin (m + 14)) : Prop where
  next : r ≠ PowerPorts.next (m + 1)
  accumulator : r ≠ PowerPorts.accumulator (m + 1)
  power : r ≠ PowerPorts.power (m + 1)
  scratch : r ≠ PowerPorts.scratch (m + 1)
  previous : r ≠ MonomialPorts.previous m
  species : r ≠ MonomialPorts.species m
  flag : r ≠ PowerBitState.flag (m + 1)

def slot (m : ℕ) : Fin (m + 14) := ⟨m + 9, by omega⟩

theorem slot_separate (m : ℕ) : Separate m (slot m) := by
  constructor
  · intro h; have hv := congrArg Fin.val h; change m + 9 = 2 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change m + 9 = 3 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change m + 9 = 4 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change m + 9 = 5 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change m + 9 = 6 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change m + 9 = 7 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change m + 9 = m + 1 + 11 at hv; omega

theorem parser_species (m : ℕ) : slot m = RoutedNetworkParser.count (m + 8) 0 := by
  apply Fin.ext
  rfl

end JointThermoComplexity.Complexity.MonomialFuel

#print axioms JointThermoComplexity.Complexity.MonomialFuel.slot_separate
