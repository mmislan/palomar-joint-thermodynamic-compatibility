module
public import proofs.JointThermoComplexity.Complexity.NaturalArraySkip

set_option autoImplicit false
@[expose] public section

/-! Exact dense-array slices around one selected literal natural field. -/

namespace JointThermoComplexity.Complexity.NaturalSelectionCode

variable {n : ℕ}

def leading (values : Fin n → ℕ) (s : Fin n) : List Bool := NaturalListSkip.code ((List.ofFn values).take s.val)

def trailing (values : Fin n → ℕ) (s : Fin n) : List Bool := NaturalListSkip.code ((List.ofFn values).drop (s.val + 1))

theorem leading_count (values : Fin n → ℕ) (s : Fin n) : ((List.ofFn values).take s.val).length = s.val := by
  simp only [List.length_take, List.length_ofFn]
  exact Nat.min_eq_left s.isLt.le

theorem split (values : Fin n → ℕ) (s : Fin n) :
    NaturalArraySkip.code values = leading values s ++ BitCodec.naturalCode (values s) ++ trailing values s := by
  have hjoin : NaturalListSkip.code ((List.ofFn values).take s.val) ++ NaturalListSkip.code ((List.ofFn values).drop s.val) =
      NaturalListSkip.code (List.ofFn values) := by
    simp only [NaturalListSkip.code, ← List.flatMap_append, List.take_append_drop]
  have hi : s.val < (List.ofFn values).length := by simpa only [List.length_ofFn] using s.isLt
  rw [NaturalListSkip.code_drop_succ _ _ hi] at hjoin
  simpa only [NaturalArraySkip.code_eq, leading, trailing, List.getElem_ofFn, List.append_assoc] using hjoin.symm

end JointThermoComplexity.Complexity.NaturalSelectionCode

#print axioms JointThermoComplexity.Complexity.NaturalSelectionCode.split
