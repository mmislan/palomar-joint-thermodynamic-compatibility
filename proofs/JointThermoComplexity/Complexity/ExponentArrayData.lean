module
public import proofs.JointThermoComplexity.Complexity.ExponentTally

set_option autoImplicit false
@[expose] public section

/-! Encoded array slices and exact monomial gate-count increments. -/

namespace JointThermoComplexity.Complexity.ExponentArrayData

def code : List ℕ → List Bool
  | [] => []
  | exponent :: rest => BitCodec.naturalCode exponent ++ code rest

def cost : List ℕ → ℕ
  | [] => 0
  | exponent :: rest => ExponentTally.fieldCost exponent + cost rest

theorem code_append (xs ys : List ℕ) : code (xs ++ ys) = code xs ++ code ys := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp only [List.cons_append, code, ih, List.append_assoc]

theorem code_eq_flatMap (values : List ℕ) : code values = values.flatMap BitCodec.naturalCode := by
  induction values with
  | nil => rfl
  | cons value rest ih => simp only [code, List.flatMap_cons, ih]

theorem finiteFunction_code {n : ℕ} (values : Fin n → ℕ) :
    (FiniteCodec.finiteFunction FiniteCodec.natural n).code values = code (List.ofFn values) := by
  simpa only [FiniteCodec.finiteFunction, FiniteCodec.natural, code_eq_flatMap] using
    FiniteCodec.functionCode_eq_flatMap FiniteCodec.natural values

theorem cost_append (xs ys : List ℕ) : cost (xs ++ ys) = cost xs + cost ys := by
  induction xs with
  | nil => simp [cost]
  | cons x rest ih => simp only [List.cons_append, cost, ih, Nat.add_assoc]

theorem take_drop_code (values : List ℕ) (i : ℕ) : code (values.take i) ++ code (values.drop i) = code values := by
  rw [← code_append, List.take_append_drop]

theorem take_code_succ (values : List ℕ) (i : ℕ) (hi : i < values.length) :
    code (values.take (i + 1)) = code (values.take i) ++ BitCodec.naturalCode values[i] := by
  rw [List.take_succ_eq_append_getElem hi, code_append]
  simp only [code, List.append_nil]

theorem take_cost_succ (values : List ℕ) (i : ℕ) (hi : i < values.length) :
    cost (values.take (i + 1)) = cost (values.take i) + ExponentTally.fieldCost values[i] := by
  rw [List.take_succ_eq_append_getElem hi, cost_append]
  simp only [cost, Nat.add_zero]

theorem drop_code (values : List ℕ) (i : ℕ) (hi : i < values.length) :
    code (values.drop i) = BitCodec.naturalCode values[i] ++ code (values.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi, code]

theorem field_length_le (values : List ℕ) (i : ℕ) (hi : i < values.length) :
    (BitCodec.naturalCode values[i]).length ≤ (code values).length := by
  have hsplit := congrArg List.length (take_drop_code values i)
  have hfield := congrArg List.length (drop_code values i hi)
  simp only [List.length_append] at hsplit hfield
  omega

theorem cost_pairs {n : ℕ} (items : List (Fin n × ℕ)) : cost (items.map Prod.snd) = ExactGateCount.monomialCost items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [List.map_cons, cost, ExponentTally.fieldCost, ExactGateCount.monomialCost, ih]

theorem cost_dense {n : ℕ} (values : Fin n → ℕ) :
    cost (List.ofFn values) = ExactGateCount.monomialCost (MonomialCircuit.denseTerms values) := by
  simpa only [MonomialCircuit.denseTerms, List.map_ofFn, Function.comp_def] using cost_pairs (MonomialCircuit.denseTerms values)

end JointThermoComplexity.Complexity.ExponentArrayData

#print axioms JointThermoComplexity.Complexity.ExponentArrayData.cost_dense
