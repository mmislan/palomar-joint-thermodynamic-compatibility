module
public import proofs.JointThermoComplexity.Complexity.ReactionTraversal
public import proofs.JointThermoComplexity.Complexity.ReactionArrayData

set_option autoImplicit false
@[expose] public section

/-! Exact prefix counts and emitted clause words for forward current-equation traversal. -/

namespace JointThermoComplexity.Complexity.CurrentTraversal

variable {n : ℕ}

def accum (count : ℕ) (items : List (ReactionCircuit.Reaction n)) (i : ℕ) : ℕ :=
  count + ExactGateCount.networkCost (items.take i)

def output (clauses : List (List Bool)) : List Bool := clauses.flatMap id

theorem accum_succ (count : ℕ) (items : List (ReactionCircuit.Reaction n)) (i : ℕ) (hi : i < items.length) :
    accum count items (i + 1) = accum count items i + ExactGateCount.reactionCost items[i] := by
  simp only [accum, ReactionArrayData.take_cost_succ items i hi, Nat.add_assoc]

theorem accum_zero (count : ℕ) (items : List (ReactionCircuit.Reaction n)) : accum count items 0 = count := by
  simp only [accum, List.take_zero, ExactGateCount.networkCost, Nat.add_zero]

theorem accum_length (count : ℕ) (items : List (ReactionCircuit.Reaction n)) :
    accum count items items.length = count + ExactGateCount.networkCost items := by simp only [accum, List.take_length]

theorem output_take_succ (clauses : List (List Bool)) (i : ℕ) (hi : i < clauses.length) :
    output (clauses.take (i + 1)) = output (clauses.take i) ++ clauses[i] := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [output, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, id_eq, List.append_nil]

end JointThermoComplexity.Complexity.CurrentTraversal

#print axioms JointThermoComplexity.Complexity.CurrentTraversal.accum_succ
