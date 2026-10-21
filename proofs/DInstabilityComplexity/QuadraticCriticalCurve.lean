module
public import proofs.DInstabilityComplexity.QuadraticPerturbation
public import proofs.DInstabilityComplexity.SixthZeroLimit

@[expose] public section

/-! # One feasible limiting vector and its constructed critical-point curve -/

namespace DInstabilityComplexity.Separation

open Filter
open scoped Topology

noncomputable section

variable {ι α : Type*} [Fintype ι] [Fintype α]

theorem exists_quadratic_critical_zero_limit (q : α → MvPolynomial ι ℤ)
    (hw : ∃ w : ι → ℝ, ∀ j, (q j).eval₂ (Int.castRingHom ℝ) w = 0) :
    ∃ x₀ : ι → ℝ, ∃ z : ℕ → ι → ℝ, ∃ t : ℕ → ℝ,
      Tendsto z atTop (𝓝 x₀) ∧ Tendsto t atTop (𝓝 0) ∧ (∀ n, 0 < t n) ∧
        (∀ n i, parameterEvaluation (t n) quadraticDenominator * z n i ^ 5 =
          (quadraticRemainder q i).eval₂ (parameterEvaluation (t n)) (z n)) ∧
        ∀ j, (q j).eval₂ (Int.castRingHom ℝ) x₀ = 0 := by
  obtain ⟨w, hw⟩ := hw
  have hwe := (quadraticEnergy_eq_zero_iff q w).mpr hw
  obtain ⟨x₀, z, t, hz, ht, hpos, hmin, hzero⟩ := exists_sixth_zero_limit
    (quadraticEnergy q) (continuous_quadraticEnergy q) (quadraticEnergy_nonneg q) w hwe
  exact ⟨x₀, z, t, hz, ht, hpos, fun n => quadratic_localMin_critical q (t n) (z n) (hmin n),
    (quadraticEnergy_eq_zero_iff q x₀).mp hzero⟩

#print axioms exists_quadratic_critical_zero_limit

end
end DInstabilityComplexity.Separation
