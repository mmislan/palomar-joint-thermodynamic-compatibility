module
public import proofs.JointThermoComplexity.Complexity.ReactionPorts
public import proofs.JointThermoComplexity.Complexity.MonomialReady

set_option autoImplicit false
@[expose] public section

/-! Natural addresses for reaction arithmetic permit the final next address to equal total arity. -/

namespace JointThermoComplexity.Complexity.ReactionGateFrame
open _root_.Complexity
open _root_.Complexity.TM
open PowerPorts MonomialPorts ReactionPorts BinaryIncrementRun

def Ready (m z prev keep : ℕ) (R : (Fin (m + 15) → Tape) → Prop) (work : Fin (m + 15) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ Register 0 (work (scratch (m + 2))) ∧ IsReg z (work (next (m + 2))) ∧
    IsReg prev (work (previous (m + 1))) ∧ IsReg keep (work (saved m)) ∧ R work

def values {arity : ℕ} (m : ℕ) (target prev keep : Fin arity) : Fin (m + 15) → Fin arity := fun j =>
  if j = next (m + 2) then target else if j = previous (m + 1) then prev else keep

theorem values_next {arity : ℕ} (m : ℕ) (target prev keep : Fin arity) : values m target prev keep (next (m + 2)) = target := by
  simp only [values, ↓reduceIte]

theorem values_previous {arity : ℕ} (m : ℕ) (target prev keep : Fin arity) : values m target prev keep (previous (m + 1)) = prev := by
  simp only [values, previous_ne_next, ↓reduceIte]

theorem values_saved {arity : ℕ} (m : ℕ) (target prev keep : Fin arity) : values m target prev keep (saved m) = keep := by
  simp only [values, saved_ne_next, saved_ne_previous, ↓reduceIte]

end JointThermoComplexity.Complexity.ReactionGateFrame

#print axioms JointThermoComplexity.Complexity.ReactionGateFrame.values_saved
