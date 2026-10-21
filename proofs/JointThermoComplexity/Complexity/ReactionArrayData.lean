module
public import proofs.JointThermoComplexity.Complexity.ReactionTallyData

set_option autoImplicit false
@[expose] public section

/-! Reaction-record slices for a register-controlled gate-count pass. -/

namespace JointThermoComplexity.Complexity.ReactionArrayData
open ReactionCircuit

variable {n : ℕ}

def code : List (Reaction n) → List Bool
  | [] => []
  | reaction :: rest => (DataCodec.reaction n).code reaction ++ code rest

theorem code_append (xs ys : List (Reaction n)) : code (xs ++ ys) = code xs ++ code ys := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp only [List.cons_append, code, ih, List.append_assoc]

theorem code_eq_flatMap (values : List (Reaction n)) :
    code values = values.flatMap (DataCodec.reaction n).code := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp only [code, List.flatMap_cons, ih]

theorem finiteFunction_code {r : ℕ} (values : Fin r → Reaction n) :
    (FiniteCodec.finiteFunction (DataCodec.reaction n) r).code values = code (List.ofFn values) := by
  simpa only [FiniteCodec.finiteFunction, code_eq_flatMap] using
    FiniteCodec.functionCode_eq_flatMap (DataCodec.reaction n) values

theorem cost_append (xs ys : List (Reaction n)) :
    ExactGateCount.networkCost (xs ++ ys) = ExactGateCount.networkCost xs + ExactGateCount.networkCost ys := by
  induction xs with
  | nil => simp [ExactGateCount.networkCost]
  | cons x rest ih => simp only [List.cons_append, ExactGateCount.networkCost, ih, Nat.add_assoc]

theorem take_drop_code (values : List (Reaction n)) (i : ℕ) :
    code (values.take i) ++ code (values.drop i) = code values := by
  rw [← code_append, List.take_append_drop]

theorem take_code_succ (values : List (Reaction n)) (i : ℕ) (hi : i < values.length) :
    code (values.take (i + 1)) = code (values.take i) ++ (DataCodec.reaction n).code values[i] := by
  rw [List.take_succ_eq_append_getElem hi, code_append]
  simp only [code, List.append_nil]

theorem take_cost_succ (values : List (Reaction n)) (i : ℕ) (hi : i < values.length) :
    ExactGateCount.networkCost (values.take (i + 1)) =
      ExactGateCount.networkCost (values.take i) + ExactGateCount.reactionCost values[i] := by
  rw [List.take_succ_eq_append_getElem hi, cost_append]
  simp only [ExactGateCount.networkCost, Nat.add_zero]

theorem drop_code (values : List (Reaction n)) (i : ℕ) (hi : i < values.length) :
    code (values.drop i) = (DataCodec.reaction n).code values[i] ++ code (values.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi, code]

theorem field_length_le (values : List (Reaction n)) (i : ℕ) (hi : i < values.length) :
    ((DataCodec.reaction n).code values[i]).length ≤ (code values).length := by
  have hsplit := congrArg List.length (take_drop_code values i)
  have hfield := congrArg List.length (drop_code values i hi)
  simp only [List.length_append] at hsplit hfield
  omega

end JointThermoComplexity.Complexity.ReactionArrayData

#print axioms JointThermoComplexity.Complexity.ReactionArrayData.finiteFunction_code
