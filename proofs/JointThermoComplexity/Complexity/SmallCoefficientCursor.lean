module
public import proofs.JointThermoComplexity.Complexity.SmallCoefficientControl

set_option autoImplicit false
@[expose] public section

/-! The finite coefficient scanner stops at the existing signed-field boundary. -/

namespace JointThermoComplexity.Complexity.SmallCoefficientCursor
open SmallCoefficientControl

theorem copied_marker (p : PayloadControl.ReadState) (hp : p ≠ .payload) (input : List Bool) :
    PayloadControl.copied p input = PayloadControl.copied .empty input := by
  cases input with
  | nil => rfl
  | cons b rest => cases p <;> cases b <;> first | rfl | contradiction

theorem rest_marker (p : PayloadControl.ReadState) (hp : p ≠ .payload) (input : List Bool) :
    NumericCursor.payloadRest p input = NumericCursor.naturalRest input := by
  cases input with
  | nil => rfl
  | cons b rest => cases p <;> cases b <;> first | rfl | contradiction

theorem scan_taken (input : List Bool) (m : Magnitude) :
    (scan m input).taken = PayloadControl.copied .empty input := by
  induction input using BitCodec.parseBits.induct generalizing m with
  | case1 => rfl
  | case2 rest => rfl
  | case3 => rfl
  | case4 b rest ih =>
    change true :: b :: (scan (push m b) rest).taken =
      true :: b :: PayloadControl.copied (PayloadControl.flag [b]) rest
    rw [ih, copied_marker (PayloadControl.flag [b]) (by cases b <;> decide)]

theorem scan_rest (input : List Bool) (m : Magnitude) :
    (scan m input).rest = NumericCursor.naturalRest input := by
  induction input using BitCodec.parseBits.induct generalizing m with
  | case1 => rfl
  | case2 rest => rfl
  | case3 => rfl
  | case4 b rest ih =>
    change (scan (push m b) rest).rest = NumericCursor.payloadRest (PayloadControl.flag [b]) rest
    rw [ih, rest_marker (PayloadControl.flag [b]) (by cases b <;> decide)]

theorem signed_taken (input : List Bool) : (signed input).2.taken = IntegerMachineRun.copied input := by
  cases input with
  | nil => rfl
  | cons b rest => simpa only [signed, IntegerMachineRun.copied] using congrArg (List.cons b) (scan_taken rest .empty)

theorem signed_rest (input : List Bool) : (signed input).2.rest = NumericCursor.integerRest input := by
  cases input with
  | nil => rfl
  | cons b rest => exact scan_rest rest .empty

theorem signed_split (input : List Bool) : (signed input).2.taken ++ (signed input).2.rest = input := by
  rw [signed_taken, signed_rest]
  exact NumericCursor.integer_split input

theorem signed_word (negate : Bool) (input : List Bool) :
    word negate (signed input).1 (signed input).2.magnitude =
      BitCodec.integerCode (if negate then -(SmallIntegerLookup.value input) else SmallIntegerLookup.value input) := by
  simp only [word, coefficient, ← signed_value_eq, signedValue]

theorem encoded (negate : Bool) (z : ℤ) (hz : z.natAbs ≤ 2) (suffix : List Bool) :
    (signed (BitCodec.integerCode z ++ suffix)).2.taken = BitCodec.integerCode z ∧
    (signed (BitCodec.integerCode z ++ suffix)).2.rest = suffix ∧
    word negate (signed (BitCodec.integerCode z ++ suffix)).1
      (signed (BitCodec.integerCode z ++ suffix)).2.magnitude = BitCodec.integerCode (if negate then -z else z) := by
  rw [signed_taken, signed_rest, NumericCursor.integer_copied_code, NumericCursor.integer_rest_code,
    signed_word, SmallIntegerLookup.value_code z hz]
  exact ⟨rfl, rfl, rfl⟩

end JointThermoComplexity.Complexity.SmallCoefficientCursor

#print axioms JointThermoComplexity.Complexity.SmallCoefficientCursor.signed_split
#print axioms JointThermoComplexity.Complexity.SmallCoefficientCursor.encoded
