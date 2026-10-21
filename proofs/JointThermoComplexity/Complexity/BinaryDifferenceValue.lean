module
public import proofs.JointThermoComplexity.Complexity.BinaryDifference

set_option autoImplicit false
@[expose] public section

/-! The final borrow is exactly signed comparison; padded subtraction has its exact integer value. -/

namespace JointThermoComplexity.Complexity.BinaryDifferenceValue
open BinaryBorrow BinaryDifference

theorem balance (xs ys : List Bool) (carry : Bool) :
    value xs - value ys - bit carry = value (subtract xs ys carry).1 -
      2 ^ max xs.length ys.length * bit (subtract xs ys carry).2 := by
  induction xs generalizing ys carry with
  | nil =>
    induction ys generalizing carry with
    | nil => simp [subtract, bit]
    | cons b ys ih =>
      have hr := ih (borrow false b carry)
      simp only [value_nil, List.length_nil, Nat.zero_max] at hr
      have hh := lift_balance (bit false) (bit b) (bit carry) (bit (digit false b carry)) (bit (borrow false b carry))
        0 (value ys) (value (subtract [] ys (borrow false b carry)).1) ys.length
        (subtract [] ys (borrow false b carry)).2 (digit_balance false b carry) hr
      simpa only [subtract, value_nil, value_cons, List.length_nil, List.length_cons, Nat.zero_max,
        show bit false = 0 from rfl, mul_zero, zero_add] using hh
  | cons a xs ih =>
    cases ys with
    | nil =>
      have hr := ih [] (borrow a false carry)
      simp only [value_nil, List.length_nil, Nat.max_zero] at hr
      have hh := lift_balance (bit a) (bit false) (bit carry) (bit (digit a false carry)) (bit (borrow a false carry))
        (value xs) 0 (value (subtract xs [] (borrow a false carry)).1) xs.length
        (subtract xs [] (borrow a false carry)).2 (digit_balance a false carry) hr
      simpa only [subtract, value_nil, value_cons, List.length_nil, List.length_cons, Nat.max_zero,
        show bit false = 0 from rfl, mul_zero, zero_add] using hh
    | cons b ys =>
      have hh := lift_balance (bit a) (bit b) (bit carry) (bit (digit a b carry)) (bit (borrow a b carry))
        (value xs) (value ys) (value (subtract xs ys (borrow a b carry)).1) (max xs.length ys.length)
        (subtract xs ys (borrow a b carry)).2 (digit_balance a b carry) (ih ys (borrow a b carry))
      simpa only [subtract, value_cons, List.length_cons, max_succ] using hh

theorem value_nonneg (xs : List Bool) : 0 ≤ value xs := by
  induction xs with
  | nil => simp only [value_nil, le_refl]
  | cons b xs ih => rw [value_cons]; have hb := bit_nonneg b; omega

theorem value_lt_pow (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    rw [value_cons, List.length_cons, pow_succ]
    have hb := bit_le_one b
    omega

theorem borrow_iff (xs ys : List Bool) : (subtract xs ys false).2 = true ↔ value xs < value ys := by
  have he := balance xs ys false
  have hn := value_nonneg (subtract xs ys false).1
  have hh := value_lt_pow (subtract xs ys false).1
  rw [output_length] at hh
  cases hf : (subtract xs ys false).2
  · have horder : ¬value xs < value ys := by simp [hf, bit] at he; omega
    simp [horder]
  · have horder : value xs < value ys := by simp [hf, bit] at he; omega
    simp [horder]

theorem no_borrow_value (xs ys : List Bool) (hf : (subtract xs ys false).2 = false) :
    value (subtract xs ys false).1 = value xs - value ys := by
  have h := balance xs ys false
  simp [hf, bit] at h
  omega

theorem reverse_no_borrow (xs ys : List Bool) (hf : (subtract xs ys false).2 = true) :
    (subtract ys xs false).2 = false := by
  have hxy := (borrow_iff xs ys).mp hf
  cases hr : (subtract ys xs false).2
  · rfl
  · have hyx := (borrow_iff ys xs).mp hr
    omega

end JointThermoComplexity.Complexity.BinaryDifferenceValue

#print axioms JointThermoComplexity.Complexity.BinaryDifferenceValue.balance
#print axioms JointThermoComplexity.Complexity.BinaryDifferenceValue.borrow_iff
#print axioms JointThermoComplexity.Complexity.BinaryDifferenceValue.no_borrow_value
