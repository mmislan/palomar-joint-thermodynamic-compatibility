module
public import proofs.DInstabilityComplexity.QuadraticCriticalCurve
public import proofs.DInstabilityComplexity.QuadraticLengthBounds
public import proofs.DInstabilityComplexity.ScaledEliminant
public import proofs.DInstabilityComplexity.EliminantLimit
public import proofs.DInstabilityComplexity.IntegerRootUpper

@[expose] public section

/-! # An effective bounded solution of every feasible closed quadratic system

All coordinate bounds apply to one common limiting solution. Neither an
algebraic witness nor a bounded solution is assumed in the feasibility premise.
The factorial height is used only in this mathematical bound; it is not an
instruction to expand that integer inside a graph-producing algorithm.
-/

namespace DInstabilityComplexity.Separation

open Filter
open scoped Topology

noncomputable section

def quadraticCoordinateHeight (n C : ℕ) : ℕ :=
  (5 ^ n).factorial * (2 * C ^ (4 * n + 1)) ^ (5 ^ n)

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

omit [Fintype ι] [Fintype α] [DecidableEq ι] in
theorem coordinateObservable_length (i : ι) :
    polynomialNumeratorLength (MvPolynomial.X i : MvPolynomial ι (Polynomial ℤ)) = 1 := by
  rw [polynomialNumeratorLength_eq_mvWeight]
  exact (integerPolynomialWeight.mvWeight_monomial (Finsupp.single i 1) 1).trans
    integerPolynomialWeight.one_eq

theorem exists_effectively_bounded_quadratic_solution (q : α → MvPolynomial ι ℤ)
    (hq : ∀ j, (q j).totalDegree ≤ 2)
    (hw : ∃ w : ι → ℝ, ∀ j, (q j).eval₂ (Int.castRingHom ℝ) w = 0) :
    ∃ x : ι → ℝ, (∀ j, (q j).eval₂ (Int.castRingHom ℝ) x = 0) ∧
      ∀ i, |x i| < (quadraticCoordinateHeight (Fintype.card ι) (quadraticCriticalLength q) : ℝ) + 1 := by
  classical
  obtain ⟨x, z, t, hz, ht, htpos, hc, hx⟩ := exists_quadratic_critical_zero_limit q hw
  refine ⟨x, hx, ?_⟩
  intro i
  let R := quadraticRemainder q
  have hR : ∀ j d, d ∈ (R j).support → monomialWeight d < 5 :=
    fun j d hd => quadraticRemainder_support_degree_lt_five q hq j d hd
  let g : MvPolynomial ι (Polynomial ℤ) := MvPolynomial.X i
  let L := 4 * Fintype.card ι + 1
  have hL : 4 * Fintype.card ι + g.totalDegree ≤ L := by
    simp only [g, MvPolynomial.totalDegree_X, L, le_refl]
  let A := multiplicationMatrix R hR quadraticDenominator g L
  let Q := scaledEliminant A (quadraticDenominator ^ L)
  have hQ : Q ≠ 0 := scaledEliminant_ne_zero _ _ (pow_ne_zero _ quadraticDenominator_ne_zero)
  have hweight : twoVariableWeight Q ≤
      quadraticCoordinateHeight (Fintype.card ι) (quadraticCriticalLength q) := by
    have hb := constructedEliminant_weight R hR quadraticDenominator g L (quadraticCriticalLength q)
      hL (quadraticDenominator_length_le q) (fun j => quadraticRemainder_length_le q hq j)
    simpa only [g, coordinateObservable_length, quadraticCoordinateHeight, L] using hb
  have hu : Tendsto (fun n => z n i) atTop (𝓝 (x i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hz
  have hroot (n : ℕ) :
      Q.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (t n)) (z n i) = 0 := by
    have hb := constructedEliminant_root R hR quadraticDenominator g L hL
      (parameterEvaluation (t n)) (z n) (hc n)
    have he : g.eval₂ (parameterEvaluation (t n)) (z n) = z n i := MvPolynomial.eval₂_X _ _ i
    rw [he] at hb
    exact hb
  obtain ⟨p, hp, hproot, hpcoeff⟩ := integer_polynomial_of_limiting_curve Q hQ t
    (fun n => z n i) (x i) (fun n => ne_of_gt (htpos n)) ht hu hroot
  exact integer_root_abs_lt_height_add_one p hp _ (fun j => (hpcoeff j).trans hweight) (x i) hproot

#print axioms coordinateObservable_length
#print axioms exists_effectively_bounded_quadratic_solution

end
end DInstabilityComplexity.Separation
