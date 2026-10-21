module
public import proofs.JointThermoComplexity.Complexity.QuadraticHomogenizationWeight
public import proofs.JointThermoComplexity.Complexity.FixedQuarterSquaring

set_option autoImplicit false
@[expose] public section

/-! # Literal integer quadratic equations force one positive quarter scale chain

Only the constants4 and1 are used. The doubly small terminal value is forced
by the equations, and is not written as a huge rational input literal.
-/

namespace JointThermoComplexity.Complexity.ExactScaleChain
open MvPolynomial FixedQuarterSquaring SourceIntegerWeight QuadraticHomogenization

noncomputable def equation (m : ℕ) : Unit ⊕ Fin m → MvPolynomial (Fin (m + 1)) ℤ :=
  Sum.elim (fun _ => C 4 * X 0 - 1) (fun j => X j.succ - X j.castSucc ^ 2)

theorem eval_initial (m : ℕ) (y : Fin (m + 1) → ℝ) :
    (equation m (.inl ())).eval₂ (Int.castRingHom ℝ) y = 4 * y 0 - 1 := by
  simp [equation]

theorem eval_successor (m : ℕ) (y : Fin (m + 1) → ℝ) (j : Fin m) :
    (equation m (.inr j)).eval₂ (Int.castRingHom ℝ) y = y j.succ - y j.castSucc ^ 2 := by
  simp [equation]

theorem roots_iff_exact (m : ℕ) (y : Fin (m + 1) → ℝ) :
    (∀ j, (equation m j).eval₂ (Int.castRingHom ℝ) y = 0) ↔
      ∀ j, y j = exactChain j.val := by
  constructor
  · intro hy
    have hinit := hy (.inl ())
    rw [eval_initial] at hinit
    have hzero : y 0 = 1 / 4 := by linarith only [hinit]
    have hvalues : ∀ k (hk : k < m + 1), y ⟨k, hk⟩ = exactChain k := by
      intro k
      induction k with
      | zero => intro _; simpa only [Fin.mk_zero, exactChain_zero] using hzero
      | succ k ih =>
        intro hk
        have hprev := ih (by omega : k < m + 1)
        have hstep : y ⟨k + 1, hk⟩ = y ⟨k, by omega⟩ ^ 2 := by
          have h := hy (.inr ⟨k, by omega⟩)
          simpa only [eval_successor, sub_eq_zero, Fin.succ_mk, Fin.castSucc_mk] using h
        rw [hstep, hprev, exactChain_succ]
    exact fun j => hvalues j.val j.isLt
  · intro hy j
    cases j with
    | inl u =>
      cases u
      rw [eval_initial, hy 0]
      simp only [Fin.val_zero, exactChain_zero]
      norm_num
    | inr j =>
      rw [eval_successor, hy j.succ, hy j.castSucc]
      change exactChain (j.val + 1) - exactChain j.val ^ 2 = 0
      rw [exactChain_succ, sub_self]

theorem exact_values_are_roots (m : ℕ) :
    ∀ j, (equation m j).eval₂ (Int.castRingHom ℝ) (fun i => exactChain i.val) = 0 :=
  (roots_iff_exact m _).mpr (fun _ => rfl)

theorem terminal_pos (m : ℕ) (y : Fin (m + 1) → ℝ)
    (hy : ∀ j, (equation m j).eval₂ (Int.castRingHom ℝ) y = 0) : 0 < y (Fin.last m) := by
  rw [(roots_iff_exact m y).mp hy (Fin.last m)]
  exact exactChain_pos m

theorem equation_degree (m : ℕ) (j : Unit ⊕ Fin m) : (equation m j).totalDegree ≤ 2 := by
  cases j with
  | inl u =>
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le _ (by simp)
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    decide
  | inr j =>
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le (by simp)
    simpa only [MvPolynomial.totalDegree_X] using
      (MvPolynomial.totalDegree_pow (X j.castSucc : MvPolynomial (Fin (m + 1)) ℤ) 2)

theorem equation_weight (m : ℕ) (j : Unit ⊕ Fin m) : weight (equation m j) ≤ 5 := by
  cases j with
  | inl u =>
    have hsub := weight_sub (C 4 * X 0 : MvPolynomial (Fin (m + 1)) ℤ) 1
    have hmul := weight_mul_X (C 4 : MvPolynomial (Fin (m + 1)) ℤ) 0
    simp only [weight_one, weight_C] at hsub hmul
    change weight (C 4 * X 0 - 1 : MvPolynomial (Fin (m + 1)) ℤ) ≤ 5
    omega
  | inr j => exact (weight_X_sub_sq _ _).trans (by decide : 2 ≤ 5)

theorem equation_count (m : ℕ) : Fintype.card (Unit ⊕ Fin m) = m + 1 := by
  rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

end JointThermoComplexity.Complexity.ExactScaleChain

#print axioms JointThermoComplexity.Complexity.ExactScaleChain.roots_iff_exact
#print axioms JointThermoComplexity.Complexity.ExactScaleChain.terminal_pos
#print axioms JointThermoComplexity.Complexity.ExactScaleChain.equation_degree
#print axioms JointThermoComplexity.Complexity.ExactScaleChain.equation_weight
