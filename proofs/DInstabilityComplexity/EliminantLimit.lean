module
public import proofs.DInstabilityComplexity.ScaledEliminant
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Algebra.Ring.Real

@[expose] public section

/-! # Nonzero integer specialization along a limiting root curve -/

namespace DInstabilityComplexity.Separation

open Polynomial Filter
open scoped Topology

noncomputable section

/-- The outer variable is the parameter; the inner variable is the value. -/
def outerEvaluation (P : Polynomial (Polynomial ℤ)) (t u : ℝ) : ℝ :=
  P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) u) t

theorem outerEvaluation_add (P Q : Polynomial (Polynomial ℤ)) (t u : ℝ) :
    outerEvaluation (P + Q) t u = outerEvaluation P t u + outerEvaluation Q t u := by
  exact Polynomial.eval₂_add _ _

theorem outerEvaluation_monomial (n : ℕ) (a : Polynomial ℤ) (t u : ℝ) :
    outerEvaluation (Polynomial.monomial n a) t u =
      a.eval₂ (Int.castRingHom ℝ) u * t ^ n := Polynomial.eval₂_monomial _ _

theorem outerEvaluation_swap (P : Polynomial (Polynomial ℤ)) (t u : ℝ) :
    outerEvaluation (Polynomial.Bivariate.swap P) t u = outerEvaluation P u t := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp only [map_add, outerEvaluation_add, hp, hq]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, outerEvaluation_add, ha, hb]
    | monomial m z =>
      rw [Polynomial.Bivariate.swap_monomial_monomial]
      simp only [outerEvaluation_monomial, Polynomial.eval₂_monomial]
      ring

theorem swap_integer_coeff (P : Polynomial (Polynomial ℤ)) (i j : ℕ) :
    ((Polynomial.Bivariate.swap P).coeff i).coeff j = (P.coeff j).coeff i := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp only [map_add, Polynomial.coeff_add, hp, hq]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, Polynomial.coeff_add, ha, hb]
    | monomial m z =>
      by_cases hn : n = j <;> by_cases hm : m = i <;>
        simp [Polynomial.Bivariate.swap_monomial_monomial, Polynomial.coeff_monomial, hn, hm]

theorem continuous_outerEvaluation (P : Polynomial (Polynomial ℤ)) :
    Continuous (fun z : ℝ × ℝ => outerEvaluation P z.1 z.2) := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq =>
    convert hp.add hq using 1
    ext z
    exact outerEvaluation_add P Q z.1 z.2
  | monomial n a =>
    have ha : Continuous (fun z : ℝ × ℝ => a.eval₂ (Int.castRingHom ℝ) z.2) :=
      (a.continuous_eval₂ (Int.castRingHom ℝ)).comp continuous_snd
    convert ha.mul (continuous_fst.pow n) using 1
    ext z
    exact outerEvaluation_monomial n a z.1 z.2

theorem exists_parameter_primitive_part (P : Polynomial (Polynomial ℤ)) (hP : P ≠ 0) :
    ∃ v : ℕ, ∃ R : Polynomial (Polynomial ℤ), P = Polynomial.X ^ v * R ∧ R.coeff 0 ≠ 0 := by
  obtain ⟨R, he, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 0
  refine ⟨P.rootMultiplicity 0, R, ?_, ?_⟩
  · simpa only [Polynomial.C_0, sub_zero] using he
  · simpa only [Polynomial.C_0, sub_zero, Polynomial.X_dvd_iff] using hnd

/-- A nonzero bivariate polynomial vanishing along a curve with nonzero
parameter tending to zero yields a nonzero bounded integer polynomial for the
limiting value. No algebraicity of that value is assumed. -/
theorem integer_polynomial_of_limiting_curve (Q : Polynomial (Polynomial ℤ)) (hQ : Q ≠ 0)
    (t u : ℕ → ℝ) (μ : ℝ) (ht : ∀ n, t n ≠ 0)
    (htlim : Tendsto t atTop (𝓝 0)) (hulim : Tendsto u atTop (𝓝 μ))
    (hroot : ∀ n, Q.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (t n)) (u n) = 0) :
    ∃ p : Polynomial ℤ, p ≠ 0 ∧ p.eval₂ (Int.castRingHom ℝ) μ = 0 ∧
      ∀ j, (p.coeff j).natAbs ≤ twoVariableWeight Q := by
  have hswap : Polynomial.Bivariate.swap Q ≠ 0 := by
    intro he
    apply hQ
    have h := congrArg Polynomial.Bivariate.swap he
    simpa only [Polynomial.Bivariate.swap_swap_apply, map_zero] using h
  obtain ⟨v, R, hfactor, hR0⟩ := exists_parameter_primitive_part _ hswap
  have hRroot : ∀ n, outerEvaluation R (t n) (u n) = 0 := by
    intro n
    have he : outerEvaluation (Polynomial.Bivariate.swap Q) (t n) (u n) = 0 := by
      rw [outerEvaluation_swap]
      exact hroot n
    rw [hfactor] at he
    have hf : t n ^ v * outerEvaluation R (t n) (u n) = 0 := by
      simpa only [outerEvaluation, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X] using he
    exact (mul_eq_zero.mp hf).resolve_left (pow_ne_zero _ (ht n))
  have hpair : Tendsto (fun n => (t n, u n)) atTop (𝓝 ((0 : ℝ), μ)) := htlim.prodMk_nhds hulim
  have hlim : Tendsto (fun n => outerEvaluation R (t n) (u n)) atTop
      (𝓝 (outerEvaluation R 0 μ)) := by
    convert (continuous_outerEvaluation R).continuousAt.tendsto.comp hpair using 1
    ext n
    rfl
  have hzlim : Tendsto (fun n => outerEvaluation R (t n) (u n)) atTop (𝓝 0) := by
    simpa only [hRroot] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hz : outerEvaluation R 0 μ = 0 := tendsto_nhds_unique hlim hzlim
  refine ⟨R.coeff 0, hR0, ?_, ?_⟩
  · simpa only [outerEvaluation, Polynomial.eval₂_at_zero, Polynomial.coe_eval₂RingHom] using hz
  · intro j
    have hc : (Polynomial.Bivariate.swap Q).coeff v = R.coeff 0 := by
      rw [hfactor]
      simpa only [zero_add] using Polynomial.coeff_X_pow_mul R v 0
    rw [← hc, swap_integer_coeff]
    exact (natAbs_coeff_le_length (Q.coeff j) v).trans
      (integerPolynomialWeight.coefficient_le_lift Q j)

#print axioms integer_polynomial_of_limiting_curve

end
end DInstabilityComplexity.Separation
