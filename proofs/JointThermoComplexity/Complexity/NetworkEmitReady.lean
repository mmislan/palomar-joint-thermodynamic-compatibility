module
public import proofs.JointThermoComplexity.Complexity.ReactionBuild

set_option autoImplicit false
@[expose] public section

/-! A network circuit may be empty, so its entry invariant stores bounded registers without requiring a gate reference. -/

namespace JointThermoComplexity.Complexity.NetworkEmitReady
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady MonomialFuel ReactionPorts

def Ready (m L offset size n : ℕ) (R : (Fin (m + 15) → Tape) → Prop)
    (work : Fin (m + 15) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
  IsReg (offset + size) (work (next (m + 2))) ∧ Temps (m + 1) L work ∧
  (∃ old, old ≤ 4 * L ∧ IsReg old (work (previous (m + 1)))) ∧
  (∃ keep, keep ≤ 4 * L ∧ IsReg keep (work (saved m))) ∧
  (∃ idx, idx ≤ L ∧ IsReg idx (work (species (m + 1)))) ∧
  IsReg n (work (MonomialFuel.slot (m + 1))) ∧ R work

end JointThermoComplexity.Complexity.NetworkEmitReady

#print axioms JointThermoComplexity.Complexity.NetworkEmitReady.Ready
