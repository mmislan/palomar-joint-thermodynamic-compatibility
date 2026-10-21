module
public import proofs.DInstabilityComplexity.TorusGradient
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! # From analytic local minima to the formal pure-power critical equations -/

namespace DInstabilityComplexity.Separation

noncomputable section

variable {ι : Type*} [DecidableEq ι]

theorem hasDerivAt_eval₂_update (p : MvPolynomial ι (Polynomial ℤ))
    (f : Polynomial ℤ →+* ℝ) (x : ι → ℝ) (i : ι) :
    HasDerivAt (fun s => p.eval₂ f (Function.update x i s))
      ((MvPolynomial.pderiv i p).eval₂ f x) (x i) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa only [MvPolynomial.pderiv_C, MvPolynomial.eval₂_C, MvPolynomial.eval₂_zero] using
      hasDerivAt_const (x i) (f a)
  | add p q hp hq =>
    convert hp.add hq using 1
    · ext s
      exact MvPolynomial.eval₂_add _ _
    · simp [map_add]
  | mul_X p j hp =>
    have hvar : HasDerivAt (fun s => Function.update x i s j)
        ((MvPolynomial.pderiv i (MvPolynomial.X j)).eval₂ f x) (x i) := by
      by_cases hj : j = i
      · subst j
        convert! hasDerivAt_id (x i) using 1 <;> simp
        rfl
      · simpa [Function.update_of_ne hj, hj] using hasDerivAt_const (x i) (x j)
    convert hp.mul hvar using 1
    · ext s
      simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Pi.mul_apply]
    · simp [Function.update_eq_self]; ring

theorem eval_pderiv_eq_zero_of_localMin (p : MvPolynomial ι (Polynomial ℤ))
    (f : Polynomial ℤ →+* ℝ) (x : ι → ℝ)
    (hx : IsLocalMin (fun y => p.eval₂ f y) x) (i : ι) :
    (MvPolynomial.pderiv i p).eval₂ f x = 0 := by
  have hu : Continuous (fun s : ℝ => Function.update x i s) := continuous_const.update i continuous_id
  have hx' : IsLocalMin (fun y => p.eval₂ f y) (Function.update x i (x i)) := by
    simpa only [Function.update_eq_self] using hx
  have hs : IsLocalMin (fun s => p.eval₂ f (Function.update x i s)) (x i) := by
    convert hx'.comp_continuous hu.continuousAt using 1
    ext s
    rfl
  exact hs.hasDerivAt_eq_zero (hasDerivAt_eval₂_update p f x i)

def parameterEvaluation (t : ℝ) : Polynomial ℤ →+* ℝ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℝ) t

theorem parameterEvaluation_C (t : ℝ) (z : ℤ) : parameterEvaluation t (Polynomial.C z) = (z : ℝ) := by
  change (Polynomial.C z).eval₂ (Int.castRingHom ℝ) t = _
  rw [Polynomial.eval₂_C]
  rfl

omit [DecidableEq ι] in
theorem eval_map_parameter (t : ℝ) (p : MvPolynomial ι ℤ) (x : ι → ℝ) :
    (MvPolynomial.map Polynomial.C p).eval₂ (parameterEvaluation t) x =
      p.eval₂ (Int.castRingHom ℝ) x := by
  have hc : (parameterEvaluation t).comp Polynomial.C = Int.castRingHom ℝ :=
    RingHom.ext fun z => parameterEvaluation_C t z
  rw [MvPolynomial.eval₂_map, hc]

def torusDenominator : Polynomial ℤ := 6 * Polynomial.X ^ 2

theorem torusDenominator_ne_zero : torusDenominator ≠ 0 := by
  simp [torusDenominator]

theorem eval_deformationPolynomial (M : Matrix (Fin r) (Fin k) ℤ) (t : ℝ)
    (x : TorusCoords k → ℝ) :
    (deformationPolynomial M).eval₂ (parameterEvaluation t) x = perturbedEnergy M t x := by
  simp only [deformationPolynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C]
  rw [eval_map_parameter, eval_map_parameter, eval_map_parameter,
    eval_penaltyPolynomial, eval_sixthPolynomial, eval_torusPolynomial]
  simp only [parameterEvaluation,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_pow]
  rfl

theorem localMin_critical_equations (M : Matrix (Fin r) (Fin k) ℤ) (t : ℝ)
    (x : TorusCoords k → ℝ) (hx : IsLocalMin (perturbedEnergy M t) x) :
    ∀ i, parameterEvaluation t torusDenominator * x i ^ 5 =
      (gradientNumerator M i).eval₂ (parameterEvaluation t) x := by
  have hf : (fun y => (deformationPolynomial M).eval₂ (parameterEvaluation t) y) =
      perturbedEnergy M t := funext (eval_deformationPolynomial M t)
  rw [← hf] at hx
  intro i
  have hz := eval_pderiv_eq_zero_of_localMin (deformationPolynomial M) (parameterEvaluation t) x hx i
  rw [deformation_gradient_shape] at hz
  change (MvPolynomial.eval₂Hom (parameterEvaluation t) x)
    (MvPolynomial.C torusDenominator * MvPolynomial.X i ^ 5 - gradientNumerator M i) = 0 at hz
  rw [map_sub, map_mul, map_pow] at hz
  simpa only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X] using sub_eq_zero.mp hz

#print axioms hasDerivAt_eval₂_update
#print axioms localMin_critical_equations

end
end DInstabilityComplexity.Separation
