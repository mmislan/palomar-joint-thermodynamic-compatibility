module
public import proofs.JointThermoComplexity.Complexity.RepeatedOutput
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceValue
public import Mathlib.Data.Nat.Size

set_option autoImplicit false
@[expose] public section

/-! Structural clipping of binary counts and exact finite output prefixes. -/

namespace JointThermoComplexity.Complexity.BoundedUnaryControl

def selected (i N : ℕ) (word : List Bool) : List Bool := if i < N then word else []

theorem bits_le (i : ℕ) : i.bits.length ≤ i := by
  simpa only [Nat.size_eq_bits_len] using (Nat.size_le.mpr (Nat.lt_two_pow_self : i < 2 ^ i))

theorem borrow_bits (i N : ℕ) : (BinaryDifference.subtract i.bits N.bits false).2 = decide (i < N) := by
  apply Bool.eq_iff_iff.mpr
  rw [BinaryDifferenceValue.borrow_iff, BinaryDifference.value_bits, BinaryDifference.value_bits]
  simp only [decide_eq_true_eq]
  omega

theorem copies_step (i N : ℕ) (word : List Bool) :
    RepeatedOutput.copies word (min i N) ++ selected i N word = RepeatedOutput.copies word (min (i + 1) N) := by
  by_cases hi : i < N
  · rw [Nat.min_eq_left (Nat.le_of_lt hi), Nat.min_eq_left (by omega), selected, ite_eq_left hi, RepeatedOutput.copies]
  · have hn : N ≤ i := by omega
    rw [Nat.min_eq_right hn, Nat.min_eq_right (by omega), selected, ite_eq_right hi, List.append_nil]

theorem copies_concat (emitted : List Bool) (i N : ℕ) (word : List Bool) :
    (emitted ++ RepeatedOutput.copies word (min i N)) ++ selected i N word =
      emitted ++ RepeatedOutput.copies word (min (i + 1) N) := by rw [List.append_assoc, copies_step]

end JointThermoComplexity.Complexity.BoundedUnaryControl

#print axioms JointThermoComplexity.Complexity.BoundedUnaryControl.borrow_bits
#print axioms JointThermoComplexity.Complexity.BoundedUnaryControl.copies_step
