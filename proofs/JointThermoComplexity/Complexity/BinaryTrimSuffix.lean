module
public import proofs.JointThermoComplexity.Complexity.BinaryTrim

set_option autoImplicit false
@[expose] public section

/-! Exact normalization equations at the most significant end of a little-endian word. -/

namespace JointThermoComplexity.Complexity.BinaryTrimSuffix

theorem append_false (xs : List Bool) : BinaryTrim.trim (xs ++ [false]) = BinaryTrim.trim xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.cons_append, BinaryTrim.trim, ih]

theorem append_true (xs : List Bool) : BinaryTrim.trim (xs ++ [true]) = xs ++ [true] := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.cons_append, BinaryTrim.trim, ih]
    cases xs <;> rfl

end JointThermoComplexity.Complexity.BinaryTrimSuffix

#print axioms JointThermoComplexity.Complexity.BinaryTrimSuffix.append_false
#print axioms JointThermoComplexity.Complexity.BinaryTrimSuffix.append_true
