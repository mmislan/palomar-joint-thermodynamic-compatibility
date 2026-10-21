module
public import proofs.JointThermoComplexity.Complexity.BinaryTrim

set_option autoImplicit false
@[expose] public section

/-! Signed subtraction uses only bit-list passes and normalization and agrees exactly with integerCode. -/

namespace JointThermoComplexity.Complexity.SignedBinaryDifference
open BinaryDifference BinaryDifferenceValue

def negative (xs ys : List Bool) : Bool := (subtract xs ys false).2

def magnitude (xs ys : List Bool) : List Bool :=
  if negative xs ys then BinaryTrim.trim (subtract ys xs false).1 else BinaryTrim.trim (subtract xs ys false).1

def code (xs ys : List Bool) : List Bool := negative xs ys :: BitCodec.encodeBits (magnitude xs ys)

theorem signed_value (xs ys : List Bool) :
    (if negative xs ys then -value (magnitude xs ys) else value (magnitude xs ys)) = value xs - value ys := by
  cases hf : (subtract xs ys false).2
  · have hv := no_borrow_value xs ys hf
    simpa only [negative, hf, Bool.false_eq_true, ↓reduceIte, magnitude, BinaryTrim.value_trim] using hv
  · have hv := no_borrow_value ys xs (reverse_no_borrow xs ys hf)
    simp only [negative, hf, ↓reduceIte, magnitude, BinaryTrim.value_trim]
    omega

theorem integerCode_negative (n : ℕ) (hn : 0 < n) : BitCodec.integerCode (-(n : ℤ)) = true :: BitCodec.naturalCode n := by
  cases n with
  | zero => omega
  | succ n => rfl

theorem code_correct (xs ys : List Bool) : code xs ys = BitCodec.integerCode (value xs - value ys) := by
  cases hf : (subtract xs ys false).2
  · have hv := no_borrow_value xs ys hf
    have hz : value xs - value ys = (BitCodec.readBits (subtract xs ys false).1 : ℤ) := hv.symm
    rw [hz]
    simp only [code, magnitude, negative, hf, Bool.false_eq_true, ↓reduceIte, BinaryTrim.canonical,
      BitCodec.integerCode, BitCodec.naturalCode]
  · have hxy := (borrow_iff xs ys).mp hf
    have hv := no_borrow_value ys xs (reverse_no_borrow xs ys hf)
    have hn : BitCodec.readBits (subtract ys xs false).1 ≠ 0 := by
      intro hzero
      have hz : value (subtract ys xs false).1 = 0 := by change (BitCodec.readBits _ : ℤ) = 0; rw [hzero]; rfl
      omega
    have hz : value xs - value ys = -(BitCodec.readBits (subtract ys xs false).1 : ℤ) := by
      change (BitCodec.readBits (subtract ys xs false).1 : ℤ) = value ys - value xs at hv
      omega
    rw [hz, integerCode_negative _ (Nat.pos_of_ne_zero hn)]
    simp only [code, magnitude, negative, hf, ↓reduceIte, BinaryTrim.canonical, BitCodec.naturalCode]

theorem naturals (left right : ℕ) : code left.bits right.bits = BitCodec.integerCode ((left : ℤ) - right) := by
  simpa only [value_bits] using code_correct left.bits right.bits

theorem magnitude_length_le (xs ys : List Bool) : (magnitude xs ys).length ≤ max xs.length ys.length := by
  cases hf : negative xs ys
  · simpa only [magnitude, hf, Bool.false_eq_true, ↓reduceIte, output_length] using BinaryTrim.length_le (subtract xs ys false).1
  · have h := BinaryTrim.length_le (subtract ys xs false).1
    rw [output_length] at h
    simpa only [magnitude, hf, ↓reduceIte, Nat.max_comm] using h

theorem code_length_le (xs ys : List Bool) : (code xs ys).length ≤ 2 * max xs.length ys.length + 2 := by
  have h := magnitude_length_le xs ys
  simp only [code, List.length_cons, BitCodec.encodeBits_length]
  omega

end JointThermoComplexity.Complexity.SignedBinaryDifference

#print axioms JointThermoComplexity.Complexity.SignedBinaryDifference.signed_value
#print axioms JointThermoComplexity.Complexity.SignedBinaryDifference.naturals
#print axioms JointThermoComplexity.Complexity.SignedBinaryDifference.code_length_le
