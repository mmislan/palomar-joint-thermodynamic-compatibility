module
public import proofs.JointThermoComplexity.Complexity.RationalFactorDispatch

set_option autoImplicit false
@[expose] public section

/-! Exact signed magnitude of a coefficient times a static template integer.
The xor convention also works when the source coefficient is zero. -/

namespace JointThermoComplexity.Complexity.SignedProductControl
open RationalFactorWords

theorem coefficient_mul (negative flip : Bool) (a b : ℕ) :
    coefficient (Bool.xor negative flip) (b * a) = coefficient negative a * coefficient flip b := by
  cases negative <;> cases flip <;> simp [coefficient, mul_comm]

theorem coefficient_product (c t : ℤ) :
    coefficient (Bool.xor (decide (c < 0)) (decide (t < 0))) (t.natAbs * c.natAbs) = c * t := by
  simpa only [RationalFactorDispatch.coefficient_sign_magnitude] using
    coefficient_mul (decide (c < 0)) (decide (t < 0)) c.natAbs t.natAbs

end JointThermoComplexity.Complexity.SignedProductControl

#print axioms JointThermoComplexity.Complexity.SignedProductControl.coefficient_product
