module
public import proofs.JointThermoComplexity.Complexity.BinaryEqualityEmit
public import proofs.JointThermoComplexity.Complexity.FiniteCodec

set_option autoImplicit false
@[expose] public section

/-! Exact shifted dense indicator words in the existing natural-array codec. -/

namespace JointThermoComplexity.Complexity.IndicatorVectorControl

def words (k M start count : ℕ) : List Bool :=
  (List.ofFn (fun j : Fin count => BinaryEqualityEmit.word k (start + j.val) M)).flatten

theorem words_zero (k M start : ℕ) : words k M start 0 = [] := rfl

theorem words_succ (k M start count : ℕ) :
    words k M start (count + 1) = words k M start count ++ BinaryEqualityEmit.word k (start + count) M := by
  unfold words
  rw [List.ofFn_succ_last, List.flatten_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, Fin.val_castSucc, Fin.val_last]

theorem words_code (k M start count : ℕ) :
    words k M start count = FiniteCodec.functionCode FiniteCodec.natural
      (fun j : Fin count => if start + j.val = M then k else 0) := by
  rw [FiniteCodec.functionCode_eq_flatMap, List.flatMap_def, List.map_ofFn]
  rfl

end JointThermoComplexity.Complexity.IndicatorVectorControl

#print axioms JointThermoComplexity.Complexity.IndicatorVectorControl.words_code
#print axioms JointThermoComplexity.Complexity.IndicatorVectorControl.words_succ
