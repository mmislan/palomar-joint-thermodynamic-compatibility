module
public import proofs.DInstabilityComplexity.TorusPenalty
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Topology.Order.LocalExtr

@[expose] public section

/-!
# Polynomial form of the deformation gradient

The parameter is an indeterminate over the integers. The gradient equations
isolate a pure fifth power with denominator `6*T^2`. Analytic identification of
formal partial derivatives at the minimizers is a subsequent bridge.
-/

namespace DInstabilityComplexity.Separation

open MvPolynomial

noncomputable section

def circlePolynomial (e : Fin k) : MvPolynomial (TorusCoords k) ℤ :=
  X (e, false) ^ 2 + X (e, true) ^ 2 + C (-1)

def penaltyPolynomial (k : ℕ) : MvPolynomial (TorusCoords k) ℤ :=
  ∑ e, circlePolynomial e ^ 2

def sixthPolynomial (k : ℕ) : MvPolynomial (TorusCoords k) ℤ :=
  ∑ i, X i ^ 6

theorem eval_penaltyPolynomial (x : TorusCoords k → ℝ) :
    (penaltyPolynomial k).eval₂ (Int.castRingHom ℝ) x = torusPenalty x := by
  simp only [penaltyPolynomial, circlePolynomial, torusPenalty, circleDefect,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_add,
    MvPolynomial.eval₂_X, MvPolynomial.eval₂_C]
  simp [sub_eq_add_neg]

theorem eval_sixthPolynomial (x : TorusCoords k → ℝ) :
    (sixthPolynomial k).eval₂ (Int.castRingHom ℝ) x = sixthRegularizer x := by
  simp [sixthPolynomial, sixthRegularizer]

theorem circlePolynomial_totalDegree_le (e : Fin k) :
    (circlePolynomial e).totalDegree ≤ 2 := by
  unfold circlePolynomial
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  · simp only [MvPolynomial.totalDegree_C]
    decide

theorem penaltyPolynomial_totalDegree_le (k : ℕ) :
    (penaltyPolynomial k).totalDegree ≤ 4 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  exact (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left 2 (circlePolynomial_totalDegree_le e))

theorem pderiv_totalDegree_le (p : MvPolynomial ι ℤ) (i : ι) :
    (pderiv i p).totalDegree ≤ p.totalDegree := by
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

theorem pderiv_sixthPolynomial (i : TorusCoords k) :
    pderiv i (sixthPolynomial k) = 6 * X i ^ 5 := by
  classical
  simp only [sixthPolynomial, map_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- The coefficient variable `Polynomial.X` is the small positive parameter. -/
def deformationPolynomial (M : Matrix (Fin r) (Fin k) ℤ) :
    MvPolynomial (TorusCoords k) (Polynomial ℤ) :=
  MvPolynomial.map Polynomial.C (penaltyPolynomial k) +
    C Polynomial.X * MvPolynomial.map Polynomial.C (torusPolynomial M) +
    C (Polynomial.X ^ 2) * MvPolynomial.map Polynomial.C (sixthPolynomial k)

def gradientNumerator (M : Matrix (Fin r) (Fin k) ℤ) (i : TorusCoords k) :
    MvPolynomial (TorusCoords k) (Polynomial ℤ) :=
  -(MvPolynomial.map Polynomial.C (pderiv i (penaltyPolynomial k)) +
    C Polynomial.X * MvPolynomial.map Polynomial.C (pderiv i (torusPolynomial M)))

theorem deformation_gradient_shape (M : Matrix (Fin r) (Fin k) ℤ) (i : TorusCoords k) :
    pderiv i (deformationPolynomial M) =
      C (6 * Polynomial.X ^ 2) * X i ^ 5 - gradientNumerator M i := by
  have h6 : (C (6 : Polynomial ℤ) : MvPolynomial (TorusCoords k) (Polynomial ℤ)) = 6 := by
    exact map_ofNat C 6
  simp [deformationPolynomial, gradientNumerator,
    MvPolynomial.pderiv_map, pderiv_sixthPolynomial, h6]
  ring

/-- The boundary exclusion proved earlier yields a genuine local minimum in
the full real coordinate space, so Fermat's theorem applies. -/
theorem box_minimizer_isLocalMin (M : Matrix (Fin r) (Fin k) ℤ) (t : ℝ)
    (ht : 0 < t) (hscale : t * (torusEnergy M (referenceCoords k) + k + 1) ≤ 1)
    (x : TorusCoords k → ℝ) (hx : IsMinOn (perturbedEnergy M t) (torusBox k) x) :
    IsLocalMin (perturbedEnergy M t) x := by
  apply hx.isLocalMin
  apply set_pi_mem_nhds Set.finite_univ
  intro i _
  have hi := abs_lt.mp (box_minimizer_interior M t ht hscale x hx i)
  exact Icc_mem_nhds hi.1 hi.2

#print axioms deformation_gradient_shape
#print axioms box_minimizer_isLocalMin

end
end DInstabilityComplexity.Separation
