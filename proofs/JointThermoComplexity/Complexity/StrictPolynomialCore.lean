module
public import proofs.JointThermoComplexity.Complexity.IntegerChainError
public import proofs.DInstabilityComplexity.QuadraticPerturbation

set_option autoImplicit false
@[expose] public section

/-! # Literal strict integer polynomials from quadratic energy and chain error

The all-real polynomial bounds its terminal coordinate through its own strict
inequality. The NO proofs use a uniform global energy gap, not a claim that
an approximate witness itself is an exact zero.
-/

namespace JointThermoComplexity.Complexity.StrictPolynomialCore
open MvPolynomial IntegerChainError FixedQuarterSquaring DInstabilityComplexity.Separation
variable {V A : Type} [Fintype A]

def InHalfCube {W : Type} (x : W → ℝ) : Prop := ∀ i, -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2

noncomputable def bounded (q : A → MvPolynomial V ℤ) (k : ℕ) : MvPolynomial (V ⊕ Fin (k + 1)) ℤ :=
  C 256 * X (.inr (Fin.last k)) ^ 2 - C 256 * rename Sum.inl (quadraticEnergyPolynomial q) -
    C 400 * rename Sum.inr (errorPolynomial k)

noncomputable def allReal (q : A → MvPolynomial V ℤ) (k : ℕ) : MvPolynomial (V ⊕ Fin (k + 1)) ℤ :=
  C 256 * X (.inr (Fin.last k)) ^ 2 * (1 - X (.inr (Fin.last k)) ^ 2) -
    C 256 * rename Sum.inl (quadraticEnergyPolynomial q) - C 400 * rename Sum.inr (errorPolynomial k)

theorem eval_bounded (q : A → MvPolynomial V ℤ) (k : ℕ) (u : V → ℝ) (y : Fin (k + 1) → ℝ) :
    (bounded q k).eval₂ (Int.castRingHom ℝ) (Sum.elim u y) =
      256 * y (Fin.last k) ^ 2 - 256 * quadraticEnergy q u -
        400 * (errorPolynomial k).eval₂ (Int.castRingHom ℝ) y := by
  simp [bounded, quadraticEnergy, MvPolynomial.eval₂_rename, Function.comp_def]

theorem eval_allReal (q : A → MvPolynomial V ℤ) (k : ℕ) (u : V → ℝ) (y : Fin (k + 1) → ℝ) :
    (allReal q k).eval₂ (Int.castRingHom ℝ) (Sum.elim u y) =
      256 * y (Fin.last k) ^ 2 * (1 - y (Fin.last k) ^ 2) - 256 * quadraticEnergy q u -
        400 * (errorPolynomial k).eval₂ (Int.castRingHom ℝ) y := by
  simp [allReal, quadraticEnergy, MvPolynomial.eval₂_rename, Function.comp_def]

theorem bounded_estimates (q : A → MvPolynomial V ℤ) (k : ℕ) (u : V → ℝ) (y : Fin (k + 1) → ℝ)
    (hp : 0 < (bounded q k).eval₂ (Int.castRingHom ℝ) (Sum.elim u y)) :
    400 * (errorPolynomial k).eval₂ (Int.castRingHom ℝ) y < 256 * y (Fin.last k) ^ 2 ∧
      quadraticEnergy q u < y (Fin.last k) ^ 2 := by
  rw [eval_bounded] at hp
  have hE := quadraticEnergy_nonneg q u
  have he := error_nonneg k y
  constructor <;> nlinarith only [hp, hE, he]

theorem allReal_estimates (q : A → MvPolynomial V ℤ) (k : ℕ) (u : V → ℝ) (y : Fin (k + 1) → ℝ)
    (hp : 0 < (allReal q k).eval₂ (Int.castRingHom ℝ) (Sum.elim u y)) :
    |y (Fin.last k)| < 1 ∧
      400 * (errorPolynomial k).eval₂ (Int.castRingHom ℝ) y < 256 * y (Fin.last k) ^ 2 ∧
        quadraticEnergy q u < y (Fin.last k) ^ 2 := by
  rw [eval_allReal] at hp
  have hE := quadraticEnergy_nonneg q u
  have he := error_nonneg k y
  have hprod : 0 < y (Fin.last k) ^ 2 * (1 - y (Fin.last k) ^ 2) := by
    nlinarith only [hp, hE, he]
  have hsq : y (Fin.last k) ^ 2 < 1 := by
    by_contra hn
    have hnprod := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (y (Fin.last k)))
      (sub_nonpos.mpr (le_of_not_gt hn))
    linarith only [hprod, hnprod]
  have habs : |y (Fin.last k)| < 1 := by nlinarith [sq_abs (y (Fin.last k)), abs_nonneg (y (Fin.last k))]
  have hprod_le : y (Fin.last k) ^ 2 * (1 - y (Fin.last k) ^ 2) ≤ y (Fin.last k) ^ 2 := by
    nlinarith only [sq_nonneg (y (Fin.last k) ^ 2)]
  refine ⟨habs, ?_, ?_⟩ <;> nlinarith only [hp, hE, he, hprod_le]

theorem half_power_step_le (k : ℕ) :
    (1 / 2 : ℝ) ^ (2 ^ (k + 1)) ≤ (1 / 2 : ℝ) ^ (2 ^ k) := by
  have hnonneg : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ k) := pow_nonneg (by norm_num) _
  have hone : (1 / 2 : ℝ) ^ (2 ^ k) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hi : (1 / 2 : ℝ) ^ (2 ^ (k + 1)) = ((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2 := by
    rw [← pow_mul, pow_succ]
  rw [hi]
  nlinarith only [hnonneg, hone]

theorem bounded_excludes_gap (q : A → MvPolynomial V ℤ) (k : ℕ)
    (hgap : ∀ u, (1 / 2 : ℝ) ^ (2 ^ k) < quadraticEnergy q u)
    (u : V → ℝ) (y : Fin (k + 1) → ℝ) (ht : |y (Fin.last k)| ≤ 1)
    (hp : 0 < (bounded q k).eval₂ (Int.castRingHom ℝ) (Sum.elim u y)) : False := by
  have h := bounded_estimates q k u y hp
  have hb := (terminal_square_bound k y ht h.1).2
  have hs := half_power_step_le k
  have hg := hgap u
  linarith only [h.2, hb, hs, hg]

theorem allReal_excludes_gap (q : A → MvPolynomial V ℤ) (k : ℕ)
    (hgap : ∀ u, (1 / 2 : ℝ) ^ (2 ^ k) < quadraticEnergy q u)
    (u : V → ℝ) (y : Fin (k + 1) → ℝ)
    (hp : 0 < (allReal q k).eval₂ (Int.castRingHom ℝ) (Sum.elim u y)) : False := by
  have h := allReal_estimates q k u y hp
  have hb := (terminal_square_bound k y h.1.le h.2.1).2
  have hs := half_power_step_le k
  have hg := hgap u
  linarith only [h.2.2, hb, hs, hg]

theorem bounded_witness (q : A → MvPolynomial V ℤ) (k : ℕ) (u : V → ℝ)
    (hu : ∀ j, (q j).eval₂ (Int.castRingHom ℝ) u = 0) :
    0 < (bounded q k).eval₂ (Int.castRingHom ℝ) (Sum.elim u (exactValues k)) := by
  have hE := (quadraticEnergy_eq_zero_iff q u).mpr hu
  rw [eval_bounded, hE, exactValues_error_zero]
  simp only [mul_zero, sub_zero]
  have hp : 0 < exactValues k (Fin.last k) := exactChain_pos (k + 1)
  exact mul_pos (by norm_num) (sq_pos_of_pos hp)

theorem allReal_witness (q : A → MvPolynomial V ℤ) (k : ℕ) (u : V → ℝ)
    (hu : ∀ j, (q j).eval₂ (Int.castRingHom ℝ) u = 0) :
    0 < (allReal q k).eval₂ (Int.castRingHom ℝ) (Sum.elim u (exactValues k)) := by
  have hE := (quadraticEnergy_eq_zero_iff q u).mpr hu
  rw [eval_allReal, hE, exactValues_error_zero]
  simp only [mul_zero, sub_zero]
  have hp : 0 < exactValues k (Fin.last k) := exactChain_pos (k + 1)
  have hq : exactValues k (Fin.last k) ≤ 1 / 4 := exactChain_le_quarter (k + 1)
  have hsq : exactValues k (Fin.last k) ^ 2 < 1 := by nlinarith only [hp, hq]
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hp)) (sub_pos.mpr hsq)

private theorem degree_C_mul {W : Type} (c : ℤ) (p : MvPolynomial W ℤ) (d : ℕ)
    (hp : p.totalDegree ≤ d) : (C c * p).totalDegree ≤ d := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simpa only [MvPolynomial.totalDegree_C, zero_add] using hp

theorem bounded_degree (q : A → MvPolynomial V ℤ) (hq : ∀ j, (q j).totalDegree ≤ 2) (k : ℕ) :
    (bounded q k).totalDegree ≤ 4 := by
  have ht : ((X (.inr (Fin.last k)) : MvPolynomial (V ⊕ Fin (k + 1)) ℤ) ^ 2).totalDegree ≤ 4 := by
    have h := MvPolynomial.totalDegree_pow (X (.inr (Fin.last k)) : MvPolynomial (V ⊕ Fin (k + 1)) ℤ) 2
    simp only [MvPolynomial.totalDegree_X] at h
    omega
  have hE := (MvPolynomial.totalDegree_rename_le (Sum.inl : V → V ⊕ Fin (k + 1)) (quadraticEnergyPolynomial q)).trans
    (quadraticEnergyPolynomial_totalDegree_le q hq)
  have he := (MvPolynomial.totalDegree_rename_le (Sum.inr : Fin (k + 1) → V ⊕ Fin (k + 1)) (errorPolynomial k)).trans (error_degree k)
  unfold bounded
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le _ (degree_C_mul 400 _ 4 he)
  exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (degree_C_mul 256 _ 4 ht) (degree_C_mul 256 _ 4 hE))

theorem allReal_degree (q : A → MvPolynomial V ℤ) (hq : ∀ j, (q j).totalDegree ≤ 2) (k : ℕ) :
    (allReal q k).totalDegree ≤ 4 := by
  have ht : ((X (.inr (Fin.last k)) : MvPolynomial (V ⊕ Fin (k + 1)) ℤ) ^ 2).totalDegree ≤ 2 := by
    simpa only [MvPolynomial.totalDegree_X] using
      MvPolynomial.totalDegree_pow (X (.inr (Fin.last k)) : MvPolynomial (V ⊕ Fin (k + 1)) ℤ) 2
  have htail : ((1 - X (.inr (Fin.last k)) ^ 2) : MvPolynomial (V ⊕ Fin (k + 1)) ℤ).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) ht)
  have hproduct : (C 256 * X (.inr (Fin.last k)) ^ 2 * (1 - X (.inr (Fin.last k)) ^ 2) :
      MvPolynomial (V ⊕ Fin (k + 1)) ℤ).totalDegree ≤ 4 :=
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (degree_C_mul 256 _ 2 ht) htail)
  have hE := (MvPolynomial.totalDegree_rename_le (Sum.inl : V → V ⊕ Fin (k + 1)) (quadraticEnergyPolynomial q)).trans
    (quadraticEnergyPolynomial_totalDegree_le q hq)
  have he := (MvPolynomial.totalDegree_rename_le (Sum.inr : Fin (k + 1) → V ⊕ Fin (k + 1)) (errorPolynomial k)).trans (error_degree k)
  unfold allReal
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le _ (degree_C_mul 400 _ 4 he)
  exact (MvPolynomial.totalDegree_sub _ _).trans (max_le hproduct (degree_C_mul 256 _ 4 hE))

end JointThermoComplexity.Complexity.StrictPolynomialCore

#print axioms JointThermoComplexity.Complexity.StrictPolynomialCore.bounded_excludes_gap
#print axioms JointThermoComplexity.Complexity.StrictPolynomialCore.allReal_excludes_gap
#print axioms JointThermoComplexity.Complexity.StrictPolynomialCore.bounded_witness
#print axioms JointThermoComplexity.Complexity.StrictPolynomialCore.allReal_witness
#print axioms JointThermoComplexity.Complexity.StrictPolynomialCore.bounded_degree
#print axioms JointThermoComplexity.Complexity.StrictPolynomialCore.allReal_degree
