module
public import proofs.JointThermoComplexity.Complexity.SmallCoefficientCursor

set_option autoImplicit false
@[expose] public section

/-! Total structural natural-field decoding into raw payload bits.
No canonicality or numeric-value assumption is needed for the length bound.
-/

namespace JointThermoComplexity.Complexity.NaturalRawControl

structure Field where
  taken : List Bool
  rest : List Bool
  bits : List Bool

def scan : List Bool → Field
  | [] => ⟨[], [], []⟩
  | false :: rest => ⟨[false], rest, []⟩
  | [true] => ⟨[true], [], []⟩
  | true :: b :: rest =>
    let next := scan rest
    ⟨true :: b :: next.taken, next.rest, b :: next.bits⟩

theorem taken_eq (input : List Bool) : (scan input).taken = PayloadControl.copied .empty input := by
  induction input using BitCodec.parseBits.induct with
  | case1 => rfl
  | case2 rest => rfl
  | case3 => rfl
  | case4 b rest ih =>
    change true :: b :: (scan rest).taken = true :: b :: PayloadControl.copied (PayloadControl.flag [b]) rest
    rw [ih, SmallCoefficientCursor.copied_marker (PayloadControl.flag [b]) (by cases b <;> decide)]

theorem rest_eq (input : List Bool) : (scan input).rest = NumericCursor.naturalRest input := by
  induction input using BitCodec.parseBits.induct with
  | case1 => rfl
  | case2 rest => rfl
  | case3 => rfl
  | case4 b rest ih =>
    change (scan rest).rest = NumericCursor.payloadRest (PayloadControl.flag [b]) rest
    rw [ih, SmallCoefficientCursor.rest_marker (PayloadControl.flag [b]) (by cases b <;> decide)]

theorem split (input : List Bool) : (scan input).taken ++ (scan input).rest = input := by
  rw [taken_eq, rest_eq]
  exact NumericCursor.natural_split input

theorem bits_length (input : List Bool) : (scan input).bits.length ≤ input.length := by
  induction input using BitCodec.parseBits.induct with
  | case1 => rfl
  | case2 rest => simp [scan]
  | case3 => simp [scan]
  | case4 b rest ih =>
    simp only [scan, List.length_cons]
    omega

theorem encoded (bits suffix : List Bool) :
    scan (BitCodec.encodeBits bits ++ suffix) = ⟨BitCodec.encodeBits bits, suffix, bits⟩ := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [BitCodec.encodeBits, scan, ih]

theorem natural (value : ℕ) (suffix : List Bool) :
    scan (BitCodec.naturalCode value ++ suffix) = ⟨BitCodec.naturalCode value, suffix, value.bits⟩ :=
  encoded value.bits suffix

end JointThermoComplexity.Complexity.NaturalRawControl

#print axioms JointThermoComplexity.Complexity.NaturalRawControl.split
#print axioms JointThermoComplexity.Complexity.NaturalRawControl.bits_length
#print axioms JointThermoComplexity.Complexity.NaturalRawControl.natural
