module
public import proofs.DInstabilityComplexity.TorusGradient
public import proofs.DInstabilityComplexity.PolynomialLength
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

/-! # Degree drop for the pure-power critical equations -/

namespace DInstabilityComplexity.Separation

open MvPolynomial

noncomputable section

theorem totalDegree_map_le {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial ι R) :
    (MvPolynomial.map f p).totalDegree ≤ p.totalDegree := by
  unfold MvPolynomial.totalDegree
  exact Finset.sup_mono (MvPolynomial.support_map_subset f p)

theorem pderiv_totalDegree_le_sub_one (p : MvPolynomial ι ℤ) (i : ι) :
    (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
  classical
  apply Finset.sup_le
  intro d hd
  have hc : (pderiv i p).coeff d ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_pderiv] at hc
  have hs : d + Finsupp.single i 1 ∈ p.support :=
    MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hdeg := MvPolynomial.le_totalDegree hs
  have he : (d + Finsupp.single i 1).sum (fun _ n => n) = d.sum (fun _ n => n) + 1 := by
    simp [Finsupp.sum_add_index]
  rw [he] at hdeg
  omega

theorem gradientNumerator_totalDegree_le (M : Matrix (Fin r) (Fin k) ℤ) (i : TorusCoords k) :
    (gradientNumerator M i).totalDegree ≤ 3 := by
  have hp : (pderiv i (penaltyPolynomial k)).totalDegree ≤ 3 :=
    (pderiv_totalDegree_le_sub_one _ _).trans
      (Nat.sub_le_sub_right (penaltyPolynomial_totalDegree_le k) 1)
  have hg : (pderiv i (torusPolynomial M)).totalDegree ≤ 1 :=
    (pderiv_totalDegree_le_sub_one _ _).trans
      (Nat.sub_le_sub_right (torusPolynomial_totalDegree_le M) 1)
  rw [gradientNumerator, MvPolynomial.totalDegree_neg]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_map_le _ _).trans hp
  · calc
      (C Polynomial.X * MvPolynomial.map Polynomial.C (pderiv i (torusPolynomial M))).totalDegree ≤
          (C Polynomial.X : MvPolynomial (TorusCoords k) (Polynomial ℤ)).totalDegree +
            (MvPolynomial.map Polynomial.C (pderiv i (torusPolynomial M))).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 0 + 1 := Nat.add_le_add (by simp) ((totalDegree_map_le _ _).trans hg)
      _ ≤ 3 := by decide

/-- Substituting a critical equation strictly decreases the total monomial
degree: a factor of degree five is replaced by degree at most three. -/
theorem gradientNumerator_support_degree_lt_five (M : Matrix (Fin r) (Fin k) ℤ)
    (i : TorusCoords k) (d : TorusCoords k →₀ ℕ)
    (hd : d ∈ (gradientNumerator M i).support) : d.sum (fun _ n => n) < 5 := by
  exact lt_of_le_of_lt ((MvPolynomial.le_totalDegree hd).trans
    (gradientNumerator_totalDegree_le M i)) (by decide)

#print axioms gradientNumerator_totalDegree_le
#print axioms gradientNumerator_support_degree_lt_five

end
end DInstabilityComplexity.Separation
