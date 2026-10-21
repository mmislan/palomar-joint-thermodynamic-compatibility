module
public import proofs.JointThermoComplexity.Complexity.BoxFrame
public import proofs.JointThermoComplexity.Complexity.CurrentTraversal

set_option autoImplicit false
@[expose] public section

/-! Exact optional-box record slices and clause prefixes for an advancing species loop. -/

namespace JointThermoComplexity.Complexity.BoxRecordTraversal
open NetworkData

def code (items : List (Option ClosedBox)) : List Bool := items.flatMap (FiniteCodec.optional DataCodec.box).code

theorem code_take_succ (items : List (Option ClosedBox)) (i : ℕ) (hi : i < items.length) :
    code (items.take (i + 1)) = code (items.take i) ++ (FiniteCodec.optional DataCodec.box).code items[i] := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [code, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem code_drop_succ (items : List (Option ClosedBox)) (i : ℕ) (hi : i < items.length) :
    code (items.drop i) = (FiniteCodec.optional DataCodec.box).code items[i] ++ code (items.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

end JointThermoComplexity.Complexity.BoxRecordTraversal

#print axioms JointThermoComplexity.Complexity.BoxRecordTraversal.code_take_succ
