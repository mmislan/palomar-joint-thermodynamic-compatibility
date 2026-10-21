module
public import proofs.JointThermoComplexity.Complexity.SourceNormalization
public import proofs.JointThermoComplexity.Complexity.SparsePolynomialCodec

set_option autoImplicit false
@[expose] public section

/-! Total encoded strict maps and polynomial output sizes for every binary input.
The runtime part of FP remains a separate requirement. -/

namespace JointThermoComplexity.Complexity.SourceTotalData
open RealSyntax SourceNormalization SparsePolynomialCodec

theorem natPolynomial_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

theorem sizeBound_mono {a b : ℕ} (h : a ≤ b) : sizeBound a ≤ sizeBound b := by
  rw [← sizePolynomial_eval a, ← sizePolynomial_eval b]
  exact natPolynomial_eval_mono sizePolynomial h

def boundedMap (input : List Bool) : List Bool := boundedCode (normalize input)
def allRealMap (input : List Bool) : List Bool := allRealCode (normalize input)

theorem boundedMap_decode (input : List Bool) :
    decode (boundedMap input) = some (boundedData (normalize input)) := decode_code _

theorem allRealMap_decode (input : List Bool) :
    decode (allRealMap input) = some (allRealData (normalize input)) := decode_code _

theorem boundedMap_length (input : List Bool) : (boundedMap input).length ≤ sizeBound (input.length + 4) :=
  Nat.le_trans (boundedCode_length _) (sizeBound_mono (normalize_code_length input))

theorem allRealMap_length (input : List Bool) : (allRealMap input).length ≤ sizeBound (input.length + 4) :=
  Nat.le_trans (allRealCode_length _) (sizeBound_mono (normalize_code_length input))

noncomputable def outputPolynomial : Polynomial ℕ := sizePolynomial.comp (Polynomial.X + 4)

theorem outputPolynomial_eval (L : ℕ) : outputPolynomial.eval L = sizeBound (L + 4) := by
  simp [outputPolynomial, Polynomial.eval_comp, sizePolynomial_eval]

theorem boundedMap_polynomial_output (input : List Bool) : (boundedMap input).length ≤ outputPolynomial.eval input.length := by
  rw [outputPolynomial_eval]
  exact boundedMap_length input

theorem allRealMap_polynomial_output (input : List Bool) : (allRealMap input).length ≤ outputPolynomial.eval input.length := by
  rw [outputPolynomial_eval]
  exact allRealMap_length input

end JointThermoComplexity.Complexity.SourceTotalData

#print axioms JointThermoComplexity.Complexity.SourceTotalData.boundedMap_decode
#print axioms JointThermoComplexity.Complexity.SourceTotalData.allRealMap_decode
#print axioms JointThermoComplexity.Complexity.SourceTotalData.boundedMap_polynomial_output
#print axioms JointThermoComplexity.Complexity.SourceTotalData.allRealMap_polynomial_output
