module
public import proofs.JointThermoComplexity.Complexity.ReactionPorts

set_option autoImplicit false
@[expose] public section

/-! The outer reaction fuel is distinct from every managed port and the nested species fuel. -/

namespace JointThermoComplexity.Complexity.ReactionFuel

structure Separate (m : ℕ) (r : Fin (m + 15)) : Prop extends MonomialFuel.Separate (m + 1) r where
  saved : r ≠ ReactionPorts.saved m
  speciesFuel : r ≠ MonomialFuel.slot (m + 1)

def slot (m : ℕ) : Fin (m + 15) := ⟨m + 11, by omega⟩

theorem slot_separate (m : ℕ) : Separate m (slot m) := by
  constructor
  · constructor
    · intro h; have hv := congrArg Fin.val h; change m + 11 = 2 at hv; omega
    · intro h; have hv := congrArg Fin.val h; change m + 11 = 3 at hv; omega
    · intro h; have hv := congrArg Fin.val h; change m + 11 = 4 at hv; omega
    · intro h; have hv := congrArg Fin.val h; change m + 11 = 5 at hv; omega
    · intro h; have hv := congrArg Fin.val h; change m + 11 = 6 at hv; omega
    · intro h; have hv := congrArg Fin.val h; change m + 11 = 7 at hv; omega
    · intro h; have hv := congrArg Fin.val h; change m + 11 = m + 2 + 11 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change m + 11 = 8 at hv; omega
  · intro h; have hv := congrArg Fin.val h; change m + 11 = m + 1 + 9 at hv; omega

theorem parser_reactions (m : ℕ) : slot m = RoutedNetworkParser.count (m + 9) 1 := by
  apply Fin.ext
  rfl

end JointThermoComplexity.Complexity.ReactionFuel

#print axioms JointThermoComplexity.Complexity.ReactionFuel.slot_separate
