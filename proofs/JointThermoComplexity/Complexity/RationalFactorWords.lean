module
public import proofs.JointThermoComplexity.Complexity.BitCodec
public import proofs.JointThermoComplexity.Complexity.RationalBranchCoefficients

set_option autoImplicit false
@[expose] public section

/-! Exact natural-code factor fields for a signed coefficient magnitude.
Both numerators and denominators are fixed before activities are chosen. -/

namespace JointThermoComplexity.Complexity.RationalFactorWords
open RationalBranchCoefficients

def coefficient (negative : Bool) (magnitude : ℕ) : ℤ :=
  if negative then -(magnitude : ℤ) else magnitude

def word (right : Bool) (c : ℤ) : List Bool :=
  BitCodec.naturalCode (if right then 2 else 1) ++
    BitCodec.naturalCode (if right then rightDenominator c else leftDenominator c)

theorem left_denominator (negative : Bool) (v : ℕ) :
    leftDenominator (coefficient negative v) = v + 1 := by
  cases negative <;> simp [coefficient, leftDenominator]

theorem right_denominator (negative : Bool) (v : ℕ) :
    rightDenominator (coefficient negative v) = if negative then 1 else 2 * v + 1 := by
  cases negative <;> simp [coefficient, rightDenominator]

theorem left_word (negative : Bool) (v : ℕ) :
    word false (coefficient negative v) = BitCodec.naturalCode 1 ++ BitCodec.naturalCode (v + 1) := by
  simp only [word, Bool.false_eq_true, ↓reduceIte, left_denominator]

theorem right_word (negative : Bool) (v : ℕ) :
    word true (coefficient negative v) = BitCodec.naturalCode 2 ++
      BitCodec.naturalCode (if negative then 1 else 2 * v + 1) := by
  simp [word, right_denominator]

end JointThermoComplexity.Complexity.RationalFactorWords

#print axioms JointThermoComplexity.Complexity.RationalFactorWords.word
#print axioms JointThermoComplexity.Complexity.RationalFactorWords.left_word
#print axioms JointThermoComplexity.Complexity.RationalFactorWords.right_word
