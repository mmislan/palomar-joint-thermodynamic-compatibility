module
public import proofs.JointThermoComplexity.Complexity.CurrentPorts
public import proofs.JointThermoComplexity.Complexity.MonomialReady

set_option autoImplicit false
@[expose] public section

/-! The rescan needs only bounded address registers, a zero binary scratch, species fuel and surrounding state. -/

namespace JointThermoComplexity.Complexity.CurrentReady
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts

def Ready (m L count idx n : ℕ) (R : (Fin (m + 15) → Tape) → Prop) (work : Fin (m + 15) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
  IsReg count (work (raw m)) ∧ IsReg idx (work (species (m + 1))) ∧
  (∃ old, old ≤ 4 * L ∧ IsReg old (work (previous (m + 1)))) ∧
  IsReg n (work (MonomialFuel.slot (m + 1))) ∧ R work

end JointThermoComplexity.Complexity.CurrentReady

#print axioms JointThermoComplexity.Complexity.CurrentReady.Ready
