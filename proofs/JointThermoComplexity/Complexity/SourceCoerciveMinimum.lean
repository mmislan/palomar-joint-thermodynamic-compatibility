module
public import proofs.JointThermoComplexity.Complexity.QuadraticWitnessBridge

set_option autoImplicit false
@[expose] public section

/-! # A limiting critical curve at the global minimum of a coercive objective

The coordinate bound is an explicit hypothesis for this analytic lemma. A
source reduction must derive it from its own polynomial construction. There
is no assumed minimizing point, minimum gap, or source-hardness certificate.
The argument extends the authenticated SixthZeroLimit compactness proof.
-/

namespace JointThermoComplexity.Complexity.SourceSeparation
open DInstabilityComplexity.Separation Filter
open scoped Topology
variable {ι : Type} [Fintype ι]

theorem exists_sixth_minimum_limit (S : (ι → ℝ) → ℝ) (hS : Continuous S)
    (hn : ∀ x, 0 ≤ S x) (C : ℝ) (hc : ∀ x i, |x i| ≤ S x + C) :
    ∃ x₀ : ι → ℝ, ∃ z : ℕ → ι → ℝ, ∃ t : ℕ → ℝ,
      Tendsto z atTop (𝓝 x₀) ∧ Tendsto t atTop (𝓝 0) ∧ (∀ n, 0 < t n) ∧
        (∀ n, IsLocalMin (sixthObjective S (t n)) (z n)) ∧ ∀ y, S x₀ ≤ S y := by
  classical
  choose xs hmin using fun n => exists_sixth_global_minimizer S hS hn
    (zeroLimitParameter n) (zeroLimitParameter_pos n)
  have hcomp (n : ℕ) : S (xs n) ≤ S 0 := by
    have hm := hmin n 0
    have hr := mul_nonneg (zeroLimitParameter_pos n).le (finiteSixthSum_nonneg (xs n))
    simp only [sixthObjective, finiteSixthSum_zero, mul_zero, add_zero] at hm
    linarith only [hm, hr]
  let R := |S 0| + |C| + 1
  have hbox (n : ℕ) : xs n ∈ realCoordinateBox R := by
    intro i _
    apply abs_le.mp
    have hx := hc (xs n) i
    have hs := le_abs_self (S 0)
    have hC := le_abs_self C
    dsimp only [R]
    linarith only [hx, hcomp n, hs, hC]
  obtain ⟨x₀, _, φ, hφ, hxlim⟩ := (isCompact_realCoordinateBox (ι := ι) R).tendsto_subseq hbox
  have hφlim : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hSlim : Tendsto (fun n => S (xs (φ n))) atTop (𝓝 (S x₀)) := by
    convert hS.continuousAt.tendsto.comp hxlim using 1
    ext n
    rfl
  refine ⟨x₀, xs ∘ φ, zeroLimitParameter ∘ φ, hxlim,
    zeroLimitParameter_tendsto.comp hφlim, fun n => zeroLimitParameter_pos (φ n), ?_, ?_⟩
  · intro n
    exact sixth_localMin_of_global S (zeroLimitParameter (φ n)) (xs (φ n)) (hmin (φ n))
  · intro y
    have hupper : Tendsto (fun n => S y + zeroLimitParameter (φ n) * finiteSixthSum y)
        atTop (𝓝 (S y)) := by
      simpa only [zero_mul, add_zero, Function.comp_def] using
        (tendsto_const_nhds.add ((zeroLimitParameter_tendsto.comp hφlim).mul_const (finiteSixthSum y)))
    apply le_of_tendsto_of_tendsto' hSlim hupper
    intro n
    have hm := hmin (φ n) y
    have hr := mul_nonneg (zeroLimitParameter_pos (φ n)).le (finiteSixthSum_nonneg (xs (φ n)))
    change S (xs (φ n)) + zeroLimitParameter (φ n) * finiteSixthSum (xs (φ n)) ≤
      S y + zeroLimitParameter (φ n) * finiteSixthSum y at hm
    linarith only [hm, hr]

variable {α : Type} [Fintype α]

theorem exists_quadratic_critical_min_limit (q : α → MvPolynomial ι ℤ) (C : ℝ)
    (hc : ∀ x i, |x i| ≤ quadraticEnergy q x + C) :
    ∃ x₀ : ι → ℝ, ∃ z : ℕ → ι → ℝ, ∃ t : ℕ → ℝ,
      Tendsto z atTop (𝓝 x₀) ∧ Tendsto t atTop (𝓝 0) ∧ (∀ n, 0 < t n) ∧
        (∀ n i, parameterEvaluation (t n) quadraticDenominator * z n i ^ 5 =
          (quadraticRemainder q i).eval₂ (parameterEvaluation (t n)) (z n)) ∧
        ∀ y, quadraticEnergy q x₀ ≤ quadraticEnergy q y := by
  obtain ⟨x₀, z, t, hz, ht, hp, hm, hmin⟩ := exists_sixth_minimum_limit
    (quadraticEnergy q) (continuous_quadraticEnergy q) (quadraticEnergy_nonneg q) C hc
  exact ⟨x₀, z, t, hz, ht, hp, fun n => quadratic_localMin_critical q (t n) (z n) (hm n), hmin⟩

end JointThermoComplexity.Complexity.SourceSeparation

#print axioms JointThermoComplexity.Complexity.SourceSeparation.exists_sixth_minimum_limit
#print axioms JointThermoComplexity.Complexity.SourceSeparation.exists_quadratic_critical_min_limit
