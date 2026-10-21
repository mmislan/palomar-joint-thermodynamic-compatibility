module
public import proofs.JointThermoComplexity.Complexity.ExponentArrayData
public import proofs.JointThermoComplexity.Complexity.DataCodec

set_option autoImplicit false
@[expose] public section

/-! Exact reaction-record syntax and component-length bounds for the tally pass. -/

namespace JointThermoComplexity.Complexity.ReactionTallyData
open ReactionCircuit ExponentArrayData

variable {n : ℕ}

def reactants (r : Reaction n) : List ℕ := List.ofFn r.reactant
def products (r : Reaction n) : List ℕ := List.ofFn r.product

theorem reaction_code (r : Reaction n) :
    (DataCodec.reaction n).code r = (code (reactants r) ++ code (products r)) ++
      (BitCodec.naturalCode r.numerator ++ BitCodec.naturalCode r.denominator) := by
  change ((FiniteCodec.finiteFunction FiniteCodec.natural n).code r.reactant ++
    (FiniteCodec.finiteFunction FiniteCodec.natural n).code r.product) ++
    (BitCodec.naturalCode r.numerator ++ BitCodec.naturalCode r.denominator) = _
  rw [finiteFunction_code, finiteFunction_code]
  rfl

theorem array_lengths (r : Reaction n) : (reactants r).length = n ∧ (products r).length = n := by
  simp only [reactants, products, List.length_ofFn, and_self]

theorem component_lengths (r : Reaction n) :
    (code (reactants r)).length ≤ ((DataCodec.reaction n).code r).length ∧
    (code (products r)).length ≤ ((DataCodec.reaction n).code r).length ∧
    (BitCodec.naturalCode r.numerator).length ≤ ((DataCodec.reaction n).code r).length ∧
    (BitCodec.naturalCode r.denominator).length ≤ ((DataCodec.reaction n).code r).length := by
  rw [reaction_code]
  simp only [List.length_append]
  omega

theorem reaction_cost (r : Reaction n) :
    ExactGateCount.reactionCost r = 6 + cost (reactants r) + cost (products r) := by
  simp only [reactants, products, cost_dense, ExactGateCount.reactionCost]

end JointThermoComplexity.Complexity.ReactionTallyData

#print axioms JointThermoComplexity.Complexity.ReactionTallyData.reaction_cost
