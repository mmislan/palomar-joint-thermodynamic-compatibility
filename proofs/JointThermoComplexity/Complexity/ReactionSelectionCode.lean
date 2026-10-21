module
public import proofs.JointThermoComplexity.Complexity.ReactionListSkip

set_option autoImplicit false
@[expose] public section

/-! Exact dense reaction-table slices around a selected literal record. -/

namespace JointThermoComplexity.Complexity.ReactionSelectionCode
open ReactionCircuit

variable {n r : ℕ}

def code (values : Fin r → Reaction n) : List Bool := ReactionArrayData.code (List.ofFn values)

def leading (values : Fin r → Reaction n) (i : Fin r) : List Bool := ReactionArrayData.code ((List.ofFn values).take i.val)

def trailing (values : Fin r → Reaction n) (i : Fin r) : List Bool := ReactionArrayData.code ((List.ofFn values).drop (i.val + 1))

theorem leading_count (values : Fin r → Reaction n) (i : Fin r) : ((List.ofFn values).take i.val).length = i.val := by
  simp only [List.length_take, List.length_ofFn]
  exact Nat.min_eq_left i.isLt.le

theorem split (values : Fin r → Reaction n) (i : Fin r) :
    code values = leading values i ++ (DataCodec.reaction n).code (values i) ++ trailing values i := by
  have hjoin := ReactionArrayData.take_drop_code (List.ofFn values) i.val
  have hi : i.val < (List.ofFn values).length := by simpa only [List.length_ofFn] using i.isLt
  rw [ReactionArrayData.drop_code _ _ hi] at hjoin
  simpa only [code, leading, trailing, List.getElem_ofFn, List.append_assoc] using hjoin.symm

end JointThermoComplexity.Complexity.ReactionSelectionCode

#print axioms JointThermoComplexity.Complexity.ReactionSelectionCode.split
