module
public import proofs.DInstabilityComplexity.QuadraticPerturbation
public import proofs.DInstabilityComplexity.MvPolynomialWeight

@[expose] public section

/-! # Explicit coefficient lengths for the quadratic critical equations -/

namespace DInstabilityComplexity.Separation

noncomputable section

variable {ι α : Type*} [Fintype α]

def quadraticSquaredLength (q : α → MvPolynomial ι ℤ) : ℕ :=
  ∑ j, integerWeight.mvWeight (q j) ^ 2

def quadraticCriticalLength (q : α → MvPolynomial ι ℤ) : ℕ :=
  6 + 4 * quadraticSquaredLength q

theorem quadraticEnergyPolynomial_integer_length_le (q : α → MvPolynomial ι ℤ) :
    integerWeight.mvWeight (quadraticEnergyPolynomial q) ≤ quadraticSquaredLength q := by
  classical
  unfold quadraticEnergyPolynomial quadraticSquaredLength
  apply (integerWeight.mvWeight_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  simpa only [pow_two] using integerWeight.mvWeight_mul_le (q j) (q j)

theorem quadraticRemainder_length_le (q : α → MvPolynomial ι ℤ)
    (hq : ∀ j, (q j).totalDegree ≤ 2) (i : ι) :
    polynomialNumeratorLength (quadraticRemainder q i) ≤ quadraticCriticalLength q := by
  have hder : integerWeight.mvWeight (MvPolynomial.pderiv i (quadraticEnergyPolynomial q)) ≤
      4 * quadraticSquaredLength q :=
    (integerWeight.mvWeight_pderiv_le _ _).trans
      (Nat.mul_le_mul (quadraticEnergyPolynomial_totalDegree_le q hq)
        (quadraticEnergyPolynomial_integer_length_le q))
  rw [polynomialNumeratorLength_eq_mvWeight, quadraticRemainder, NatRingWeight.mvWeight_neg]
  exact ((mapped_integer_mvWeight_le _).trans hder).trans (Nat.le_add_left _ _)

omit [Fintype α] in
theorem quadraticDenominator_length : coefficientLength quadraticDenominator = 6 := by
  have he : quadraticDenominator = Polynomial.monomial 1 (6 : ℤ) := by
    simpa only [quadraticDenominator, pow_one, map_ofNat] using
      (Polynomial.C_mul_X_pow_eq_monomial :
        Polynomial.C (6 : ℤ) * Polynomial.X ^ 1 = Polynomial.monomial 1 (6 : ℤ))
  rw [he, coefficientLength_monomial]
  decide

theorem quadraticDenominator_length_le (q : α → MvPolynomial ι ℤ) :
    coefficientLength quadraticDenominator ≤ quadraticCriticalLength q := by
  rw [quadraticDenominator_length]
  exact Nat.le_add_right _ _

#print axioms quadraticEnergyPolynomial_integer_length_le
#print axioms quadraticRemainder_length_le
#print axioms quadraticDenominator_length_le

end
end DInstabilityComplexity.Separation
