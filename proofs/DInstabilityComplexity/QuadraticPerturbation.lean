module
public import proofs.DInstabilityComplexity.CoerciveSixthMinimum
public import proofs.DInstabilityComplexity.TorusDerivative
public import proofs.DInstabilityComplexity.GradientBounds

@[expose] public section

/-! # Integer-polynomial critical equations for closed quadratic feasibility -/

namespace DInstabilityComplexity.Separation

open MvPolynomial

noncomputable section

variable {ι α : Type*} [Fintype α]

def quadraticEnergyPolynomial (q : α → MvPolynomial ι ℤ) : MvPolynomial ι ℤ :=
  ∑ j, q j ^ 2

def quadraticEnergy (q : α → MvPolynomial ι ℤ) (x : ι → ℝ) : ℝ :=
  (quadraticEnergyPolynomial q).eval₂ (Int.castRingHom ℝ) x

theorem quadraticEnergy_eq_sum (q : α → MvPolynomial ι ℤ) (x : ι → ℝ) :
    quadraticEnergy q x = ∑ j, ((q j).eval₂ (Int.castRingHom ℝ) x) ^ 2 := by
  simp only [quadraticEnergy, quadraticEnergyPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_pow]

theorem quadraticEnergy_nonneg (q : α → MvPolynomial ι ℤ) (x : ι → ℝ) :
    0 ≤ quadraticEnergy q x := by
  rw [quadraticEnergy_eq_sum]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem quadraticEnergy_eq_zero_iff (q : α → MvPolynomial ι ℤ) (x : ι → ℝ) :
    quadraticEnergy q x = 0 ↔ ∀ j, (q j).eval₂ (Int.castRingHom ℝ) x = 0 := by
  simp only [quadraticEnergy_eq_sum,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _),
    Finset.mem_univ, forall_const, sq_eq_zero_iff]

theorem continuous_quadraticEnergy (q : α → MvPolynomial ι ℤ) : Continuous (quadraticEnergy q) := by
  unfold quadraticEnergy
  simpa only [MvPolynomial.eval_map] using
    (MvPolynomial.map (Int.castRingHom ℝ) (quadraticEnergyPolynomial q)).continuous_eval

theorem quadraticEnergyPolynomial_totalDegree_le (q : α → MvPolynomial ι ℤ)
    (hq : ∀ j, (q j).totalDegree ≤ 2) : (quadraticEnergyPolynomial q).totalDegree ≤ 4 := by
  unfold quadraticEnergyPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hq j))

variable [Fintype ι]

def coordinateSixthPolynomial : MvPolynomial ι ℤ := ∑ i, X i ^ 6

theorem eval_coordinateSixthPolynomial (x : ι → ℝ) :
    (coordinateSixthPolynomial (ι := ι)).eval₂ (Int.castRingHom ℝ) x = finiteSixthSum x := by
  simp [coordinateSixthPolynomial, finiteSixthSum]

theorem pderiv_coordinateSixthPolynomial (i : ι) :
    pderiv i (coordinateSixthPolynomial (ι := ι)) = 6 * X i ^ 5 := by
  classical
  simp only [coordinateSixthPolynomial, map_sum]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

def quadraticDeformation (q : α → MvPolynomial ι ℤ) : MvPolynomial ι (Polynomial ℤ) :=
  MvPolynomial.map Polynomial.C (quadraticEnergyPolynomial q) +
    C Polynomial.X * MvPolynomial.map Polynomial.C (coordinateSixthPolynomial (ι := ι))

def quadraticRemainder (q : α → MvPolynomial ι ℤ) (i : ι) : MvPolynomial ι (Polynomial ℤ) :=
  -(MvPolynomial.map Polynomial.C (pderiv i (quadraticEnergyPolynomial q)))

def quadraticDenominator : Polynomial ℤ := 6 * Polynomial.X

theorem quadraticDenominator_ne_zero : quadraticDenominator ≠ 0 := by simp [quadraticDenominator]

theorem quadratic_deformation_gradient_shape (q : α → MvPolynomial ι ℤ) (i : ι) :
    pderiv i (quadraticDeformation q) = C quadraticDenominator * X i ^ 5 - quadraticRemainder q i := by
  have h6 : (C (6 : Polynomial ℤ) : MvPolynomial ι (Polynomial ℤ)) = 6 := map_ofNat C 6
  simp [quadraticDeformation, quadraticRemainder, quadraticDenominator,
    MvPolynomial.pderiv_map, pderiv_coordinateSixthPolynomial, h6]
  ring

omit [Fintype ι] in
theorem quadraticRemainder_totalDegree_le (q : α → MvPolynomial ι ℤ)
    (hq : ∀ j, (q j).totalDegree ≤ 2) (i : ι) : (quadraticRemainder q i).totalDegree ≤ 3 := by
  rw [quadraticRemainder, MvPolynomial.totalDegree_neg]
  exact (totalDegree_map_le _ _).trans ((pderiv_totalDegree_le_sub_one _ _).trans
    (Nat.sub_le_sub_right (quadraticEnergyPolynomial_totalDegree_le q hq) 1))

omit [Fintype ι] in
theorem quadraticRemainder_support_degree_lt_five (q : α → MvPolynomial ι ℤ)
    (hq : ∀ j, (q j).totalDegree ≤ 2) (i : ι) (d : ι →₀ ℕ)
    (hd : d ∈ (quadraticRemainder q i).support) : d.sum (fun _ n => n) < 5 :=
  lt_of_le_of_lt ((MvPolynomial.le_totalDegree hd).trans (quadraticRemainder_totalDegree_le q hq i))
    (by decide)

theorem eval_quadraticDeformation (q : α → MvPolynomial ι ℤ) (ε : ℝ) (x : ι → ℝ) :
    (quadraticDeformation q).eval₂ (parameterEvaluation ε) x = sixthObjective (quadraticEnergy q) ε x := by
  simp only [quadraticDeformation, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  rw [eval_map_parameter, eval_map_parameter, eval_coordinateSixthPolynomial]
  simp only [parameterEvaluation, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl

theorem quadratic_localMin_critical (q : α → MvPolynomial ι ℤ) (ε : ℝ) (x : ι → ℝ)
    (hx : IsLocalMin (sixthObjective (quadraticEnergy q) ε) x) :
    ∀ i, parameterEvaluation ε quadraticDenominator * x i ^ 5 =
      (quadraticRemainder q i).eval₂ (parameterEvaluation ε) x := by
  classical
  have hf : (fun y => (quadraticDeformation q).eval₂ (parameterEvaluation ε) y) =
      sixthObjective (quadraticEnergy q) ε := funext (eval_quadraticDeformation q ε)
  rw [← hf] at hx
  intro i
  have hz := eval_pderiv_eq_zero_of_localMin (quadraticDeformation q) (parameterEvaluation ε) x hx i
  rw [quadratic_deformation_gradient_shape] at hz
  change (MvPolynomial.eval₂Hom (parameterEvaluation ε) x)
    (C quadraticDenominator * X i ^ 5 - quadraticRemainder q i) = 0 at hz
  rw [map_sub, map_mul, map_pow] at hz
  simpa only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
    using sub_eq_zero.mp hz

#print axioms quadraticEnergy_eq_zero_iff
#print axioms quadraticRemainder_totalDegree_le
#print axioms quadratic_localMin_critical

end
end DInstabilityComplexity.Separation
