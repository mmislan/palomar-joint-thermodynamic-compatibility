module
public import proofs.JointThermoComplexity.Complexity.BinaryBorrow
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! Bitwise padded subtraction has output length equal to the larger input bit length. -/

namespace JointThermoComplexity.Complexity.BinaryDifference
open BinaryBorrow

def value (bits : List Bool) : ℤ := BitCodec.readBits bits

@[simp] theorem value_nil : value [] = 0 := rfl

theorem value_cons (b : Bool) (rest : List Bool) : value (b :: rest) = bit b + 2 * value rest := by
  cases b <;> simp [value, BitCodec.readBits, Nat.bit_val, bit, add_comm]

theorem value_bits (n : ℕ) : value n.bits = (n : ℤ) := by rw [value, BitCodec.readBits_bits]

theorem max_succ (a b : ℕ) : max (a + 1) (b + 1) = max a b + 1 := by omega

def subtract : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], carry => ([], carry)
  | left :: xs, [], carry =>
      let rest := subtract xs [] (borrow left false carry)
      (digit left false carry :: rest.1, rest.2)
  | [], right :: ys, carry =>
      let rest := subtract [] ys (borrow false right carry)
      (digit false right carry :: rest.1, rest.2)
  | left :: xs, right :: ys, carry =>
      let rest := subtract xs ys (borrow left right carry)
      (digit left right carry :: rest.1, rest.2)
termination_by xs ys _ => xs.length + ys.length

theorem output_length (xs ys : List Bool) (carry : Bool) :
    (subtract xs ys carry).1.length = max xs.length ys.length := by
  induction xs generalizing ys carry with
  | nil =>
    induction ys generalizing carry with
    | nil => simp [subtract]
    | cons b ys ih => simpa only [subtract, List.length_cons, List.length_nil, Nat.zero_max] using congrArg (fun n => n + 1) (ih (borrow false b carry))
  | cons a xs ih =>
    cases ys with
    | nil => simpa only [subtract, List.length_cons, List.length_nil, Nat.max_zero] using congrArg (fun n => n + 1) (ih [] (borrow a false carry))
    | cons b ys =>
        have hh := congrArg (fun n => n + 1) (ih ys (borrow a b carry))
        simpa only [subtract, List.length_cons, max_succ] using hh

theorem lift_balance (a b carry d next left right result : ℤ) (width : ℕ) (last : Bool)
    (hd : a - b - carry = d - 2 * next)
    (hr : left - right - next = result - 2 ^ width * bit last) :
    (a + 2 * left) - (b + 2 * right) - carry = (d + 2 * result) - 2 ^ (width + 1) * bit last := by
  calc (a + 2 * left) - (b + 2 * right) - carry = (a - b - carry) + 2 * (left - right) := by ring1
       _ = (d - 2 * next) + 2 * (left - right) := by rw [hd]
       _ = d + 2 * (left - right - next) := by ring1
       _ = d + 2 * (result - 2 ^ width * bit last) := by rw [hr]
       _ = _ := by rw [pow_succ]; ring1

end JointThermoComplexity.Complexity.BinaryDifference

#print axioms JointThermoComplexity.Complexity.BinaryDifference.output_length
#print axioms JointThermoComplexity.Complexity.BinaryDifference.lift_balance
