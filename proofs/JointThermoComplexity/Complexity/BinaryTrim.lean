module
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceValue
public import proofs.JointThermoComplexity.Complexity.CanonicalBits

set_option autoImplicit false
@[expose] public section

/-! Remove high zero digits without changing value; normalization yields the exact canonical Nat.bits payload. -/

namespace JointThermoComplexity.Complexity.BinaryTrim
open BinaryBorrow BinaryDifference

def trim : List Bool → List Bool
  | [] => []
  | b :: xs => match trim xs, b with
      | [], false => []
      | rest, _ => b :: rest

theorem valid (xs : List Bool) : CanonicalBits.validPayload (trim xs) = true := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases ht : trim xs with
    | nil => cases b <;> simp [trim, ht, CanonicalBits.validPayload]
    | cons c rest =>
      have hh : CanonicalBits.validPayload (c :: rest) = true := by simpa only [ht] using ih
      simpa only [trim, ht, CanonicalBits.validPayload] using hh

theorem length_le (xs : List Bool) : (trim xs).length ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases ht : trim xs with
    | nil => cases b <;> simp [trim, ht]
    | cons c rest =>
      rw [ht] at ih
      simpa only [trim, ht, List.length_cons] using Nat.add_le_add_right ih 1

theorem value_trim (xs : List Bool) : value (trim xs) = value xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases ht : trim xs with
    | nil =>
      rw [value_cons, ← ih, ht, value_nil]
      cases b <;> simp [trim, ht, value, BitCodec.readBits, Nat.bit_val, bit]
    | cons c rest =>
      rw [ht] at ih
      simpa only [trim, ht, value_cons] using congrArg (fun v => bit b + 2 * v) ih

theorem canonical (xs : List Bool) : trim xs = (BitCodec.readBits xs).bits := by
  have hn : BitCodec.readBits (trim xs) = BitCodec.readBits xs := congrArg Int.toNat (value_trim xs)
  have hc := CanonicalBits.bits_readBits_of_valid (trim xs) (valid xs)
  rw [hn] at hc
  exact hc.symm

end JointThermoComplexity.Complexity.BinaryTrim

#print axioms JointThermoComplexity.Complexity.BinaryTrim.value_trim
#print axioms JointThermoComplexity.Complexity.BinaryTrim.canonical
