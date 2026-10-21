module
public import proofs.JointThermoComplexity.Complexity.NaturalCanonicalLoad
public import proofs.JointThermoComplexity.Complexity.SourceBitRead

set_option autoImplicit false
@[expose] public section

/-! Total signed-field control. The sign consumes at most one bit and the
magnitude consumes one raw natural field. Canonical encodings agree with the
integer codec; malformed encodings still have bounded canonical magnitudes. -/

namespace JointThermoComplexity.Complexity.SignedRawControl

def negative (input : List Bool) : Bool := SourceBitRead.value input

def taken (input : List Bool) : List Bool :=
  BooleanMachine.copied input ++ (NaturalRawControl.scan (BooleanMachine.suffix input)).taken

def rest (input : List Bool) : List Bool :=
  (NaturalRawControl.scan (BooleanMachine.suffix input)).rest

def magnitude (input : List Bool) : ℕ :=
  NaturalCanonicalLoad.value (BooleanMachine.suffix input)

theorem split (input : List Bool) : taken input ++ rest input = input := by
  rw [taken, rest, List.append_assoc, NaturalRawControl.split, BooleanMachine.consumed_and_suffix]

theorem suffix_length (input : List Bool) : (BooleanMachine.suffix input).length ≤ input.length := by
  cases input <;> simp [BooleanMachine.suffix]

theorem magnitude_bits_length (input : List Bool) : (magnitude input).bits.length ≤ input.length :=
  (NaturalCanonicalLoad.bits_length _).trans (suffix_length input)

theorem rest_length (input : List Bool) : (rest input).length ≤ input.length := by
  have h := congrArg List.length (split input)
  simp only [List.length_append] at h
  omega

@[simp] theorem taken_integer (c : ℤ) (suffix : List Bool) :
    taken (BitCodec.integerCode c ++ suffix) = BitCodec.integerCode c := by
  cases c <;> simp [taken, BitCodec.integerCode, BooleanMachine.copied,
    BooleanMachine.suffix, NaturalRawControl.natural]

@[simp] theorem rest_integer (c : ℤ) (suffix : List Bool) :
    rest (BitCodec.integerCode c ++ suffix) = suffix := by
  cases c <;> simp [rest, BitCodec.integerCode, BooleanMachine.suffix, NaturalRawControl.natural]

@[simp] theorem negative_integer (c : ℤ) (suffix : List Bool) :
    negative (BitCodec.integerCode c ++ suffix) = decide (c < 0) := by
  cases c <;> simp [negative, BitCodec.integerCode, SourceBitRead.value]

@[simp] theorem magnitude_integer (c : ℤ) (suffix : List Bool) :
    magnitude (BitCodec.integerCode c ++ suffix) = c.natAbs := by
  cases c <;> simp [magnitude, BitCodec.integerCode, BooleanMachine.suffix,
    NaturalCanonicalLoad.value, NaturalRawControl.natural]

@[simp] theorem available_integer (c : ℤ) (suffix : List Bool) :
    BooleanMachine.accepted (BitCodec.integerCode c ++ suffix) = true := by
  cases c <;> rfl

end JointThermoComplexity.Complexity.SignedRawControl

#print axioms JointThermoComplexity.Complexity.SignedRawControl.split
#print axioms JointThermoComplexity.Complexity.SignedRawControl.magnitude_bits_length
#print axioms JointThermoComplexity.Complexity.SignedRawControl.magnitude_integer
