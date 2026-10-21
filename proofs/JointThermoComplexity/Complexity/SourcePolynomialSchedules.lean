module
public import proofs.JointThermoComplexity.Complexity.BitCodec
public import Mathlib.Algebra.Ring.Nat

set_option autoImplicit false
@[expose] public section

/-! # Executable polynomial scale and threshold lengths

The effective witness and gap proofs are imported only by the semantic bridge.
These data functions contain the already derived explicit natural polynomials.
-/

namespace JointThermoComplexity.Complexity.SourcePolynomialSchedules

def scaleLength (L : ℕ) : ℕ := 60 * L ^ 2 + 265 * L + 58
def thresholdLength (L : ℕ) : ℕ :=
  57600 * L ^ 4 + 518880 * L ^ 3 + 1291320 * L ^ 2 + 552897 * L + 65106

end JointThermoComplexity.Complexity.SourcePolynomialSchedules

#print axioms JointThermoComplexity.Complexity.SourcePolynomialSchedules.scaleLength
#print axioms JointThermoComplexity.Complexity.SourcePolynomialSchedules.thresholdLength
