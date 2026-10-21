module
public import proofs.JointThermoComplexity.Complexity.BitCodec

set_option autoImplicit false
@[expose] public section

/-! A finite full-subtractor transition and its exact signed digit balance. -/

namespace JointThermoComplexity.Complexity.BinaryBorrow

def bit (b : Bool) : ℤ := if b then 1 else 0

def digit (left right carry : Bool) : Bool := Bool.xor (Bool.xor left right) carry

def borrow (left right carry : Bool) : Bool := ((!left) && (right || carry)) || (right && carry)

theorem digit_balance (left right carry : Bool) :
    bit left - bit right - bit carry = bit (digit left right carry) - 2 * bit (borrow left right carry) := by
  cases left <;> cases right <;> cases carry <;> decide

theorem bit_nonneg (b : Bool) : 0 ≤ bit b := by cases b <;> decide

theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> decide

end JointThermoComplexity.Complexity.BinaryBorrow

#print axioms JointThermoComplexity.Complexity.BinaryBorrow.digit_balance
