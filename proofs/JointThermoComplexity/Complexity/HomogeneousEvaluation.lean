module
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

set_option autoImplicit false
@[expose] public section

/-! # Evaluation of a homogeneous integer polynomial at one shared scale -/

namespace JointThermoComplexity.Complexity.HomogeneousEvaluation
open MvPolynomial
variable {V : Type}

theorem eval_scale (p : MvPolynomial V ℤ) (d : ℕ) (hp : p.IsHomogeneous d)
    (s : ℝ) (x : V → ℝ) :
    p.eval₂ (Int.castRingHom ℝ) (fun i => s * x i) =
      s ^ d * p.eval₂ (Int.castRingHom ℝ) x := by
  classical
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hdegree : ∑ i ∈ e.support, e i = d := by
    have h := hp (MvPolynomial.mem_support_iff.mp he)
    simpa only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum] using h
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdegree]
  ring

theorem component_eval_scale (p : MvPolynomial V ℤ) (d : ℕ) (s : ℝ) (x : V → ℝ) :
    (homogeneousComponent d p).eval₂ (Int.castRingHom ℝ) (fun i => s * x i) =
      s ^ d * (homogeneousComponent d p).eval₂ (Int.castRingHom ℝ) x :=
  eval_scale _ _ (homogeneousComponent_isHomogeneous d p) s x

theorem quadratic_components (p : MvPolynomial V ℤ) (hp : p.totalDegree ≤ 2) :
    homogeneousComponent 0 p + homogeneousComponent 1 p + homogeneousComponent 2 p = p := by
  classical
  ext e
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_homogeneousComponent]
  by_cases he : p.coeff e = 0
  · simp only [he, ite_self, add_zero]
  · have hs : e ∈ p.support := MvPolynomial.mem_support_iff.mpr he
    have hd : e.degree ≤ 2 := by
      have h := (MvPolynomial.le_totalDegree hs).trans hp
      simpa only [Finsupp.degree_apply, Finsupp.sum] using h
    have hcases : e.degree = 0 ∨ e.degree = 1 ∨ e.degree = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · simp [hzero]
    · simp [hone]
    · simp [htwo]

end JointThermoComplexity.Complexity.HomogeneousEvaluation

#print axioms JointThermoComplexity.Complexity.HomogeneousEvaluation.eval_scale
#print axioms JointThermoComplexity.Complexity.HomogeneousEvaluation.quadratic_components
