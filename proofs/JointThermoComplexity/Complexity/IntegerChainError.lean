module
public import proofs.JointThermoComplexity.Complexity.QuadraticHomogenizationWeight
public import proofs.JointThermoComplexity.Complexity.FixedQuarterSquaring

set_option autoImplicit false
@[expose] public section

/-! # Literal integer quartic error for fixed-quarter approximate squaring

The first variable represents y1, with y0 fixed to1/4. Multiplying every
quadratic edge by16 clears the only denominator. The resulting sum of squares
evaluates to256 times the real finite-chain error used by the checked bound.
-/

namespace JointThermoComplexity.Complexity.IntegerChainError
open MvPolynomial FixedQuarterSquaring SourceIntegerWeight QuadraticHomogenization
open DInstabilityComplexity.Separation

noncomputable def sequence (k : ℕ) (y : Fin (k + 1) → ℝ) : ℕ → ℝ
  | 0 => 1 / 4
  | i + 1 => if hi : i < k + 1 then y ⟨i, hi⟩ else 0

@[simp] theorem sequence_zero (k : ℕ) (y : Fin (k + 1) → ℝ) : sequence k y 0 = 1 / 4 := rfl

theorem sequence_succ (k : ℕ) (y : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    sequence k y (i.val + 1) = y i := by
  simp only [sequence, dite_eq_left i.isLt]

theorem sequence_one (k : ℕ) (y : Fin (k + 1) → ℝ) : sequence k y 1 = y 0 := by
  simpa only [Fin.val_zero, zero_add] using sequence_succ k y 0

theorem sequence_terminal (k : ℕ) (y : Fin (k + 1) → ℝ) :
    sequence k y (k + 1) = y (Fin.last k) := sequence_succ k y (Fin.last k)

noncomputable def edge (k : ℕ) (i : Fin (k + 1)) : MvPolynomial (Fin (k + 1)) ℤ :=
  Fin.cases (C 16 * X 0 - 1) (fun j => C 16 * (X j.succ - X j.castSucc ^ 2)) i

@[simp] theorem edge_zero (k : ℕ) : edge k 0 = C 16 * X 0 - 1 := by simp only [edge, Fin.cases_zero]

@[simp] theorem edge_succ (k : ℕ) (j : Fin k) :
    edge k j.succ = C 16 * (X j.succ - X j.castSucc ^ 2) := by simp only [edge, Fin.cases_succ]

theorem eval_edge_zero (k : ℕ) (y : Fin (k + 1) → ℝ) :
    (edge k 0).eval₂ (Int.castRingHom ℝ) y = 16 * y 0 - 1 := by simp [edge_zero]

theorem eval_edge_succ (k : ℕ) (y : Fin (k + 1) → ℝ) (j : Fin k) :
    (edge k j.succ).eval₂ (Int.castRingHom ℝ) y = 16 * (y j.succ - y j.castSucc ^ 2) := by
  simp [edge_succ]

theorem eval_edge (k : ℕ) (y : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    (edge k i).eval₂ (Int.castRingHom ℝ) y =
      16 * (sequence k y (i.val + 1) - sequence k y i.val ^ 2) := by
  refine Fin.cases ?_ ?_ i
  · rw [eval_edge_zero]
    simp only [Fin.val_zero, zero_add, sequence_one, sequence_zero]
    ring
  · intro j
    rw [eval_edge_succ]
    simp only [Fin.val_succ]
    have hc := sequence_succ k y j.succ
    have hp := sequence_succ k y j.castSucc
    simp only [Fin.val_succ] at hc
    simp only [Fin.val_castSucc] at hp
    rw [hc, hp]

noncomputable def errorPolynomial (k : ℕ) : MvPolynomial (Fin (k + 1)) ℤ := ∑ i, edge k i ^ 2

theorem eval_errorPolynomial (k : ℕ) (y : Fin (k + 1) → ℝ) :
    (errorPolynomial k).eval₂ (Int.castRingHom ℝ) y = 256 * chainError (sequence k y) (k + 1) := by
  have hsum : (∑ i : Fin (k + 1), (sequence k y (i.val + 1) - sequence k y i.val ^ 2) ^ 2) =
      ∑ j ∈ Finset.range (k + 1), (sequence k y (j + 1) - sequence k y j ^ 2) ^ 2 := by
    apply Finset.sum_bij (fun (i : Fin (k + 1)) _ => i.val)
    · intro i _
      exact Finset.mem_range.mpr i.isLt
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro b hb
      exact ⟨⟨b, Finset.mem_range.mp hb⟩, Finset.mem_univ _, rfl⟩
    · intro i _
      rfl
  have heval : (errorPolynomial k).eval₂ (Int.castRingHom ℝ) y =
      ∑ i : Fin (k + 1), 256 * (sequence k y (i.val + 1) - sequence k y i.val ^ 2) ^ 2 := by
    simp only [errorPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_pow, eval_edge]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← Finset.mul_sum, hsum] at heval
  exact heval

theorem error_nonneg (k : ℕ) (y : Fin (k + 1) → ℝ) :
    0 ≤ (errorPolynomial k).eval₂ (Int.castRingHom ℝ) y := by
  rw [eval_errorPolynomial]
  exact mul_nonneg (by norm_num) (chainError_nonneg _ _)

theorem terminal_square_bound (k : ℕ) (y : Fin (k + 1) → ℝ)
    (ht : |y (Fin.last k)| ≤ 1)
    (he : 400 * (errorPolynomial k).eval₂ (Int.castRingHom ℝ) y < 256 * y (Fin.last k) ^ 2) :
    0 < y (Fin.last k) ^ 2 ∧ y (Fin.last k) ^ 2 ≤ (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
  have herr : 400 * chainError (sequence k y) (k + 1) < sequence k y (k + 1) ^ 2 := by
    rw [eval_errorPolynomial] at he
    rw [sequence_terminal]
    nlinarith only [he]
  have h := terminal_square_le_of_sum (sequence k y) (k + 1) (sequence_zero k y)
    (by simpa only [sequence_terminal] using ht) herr
  simpa only [sequence_terminal] using h

theorem edge_degree (k : ℕ) (i : Fin (k + 1)) : (edge k i).totalDegree ≤ 2 := by
  refine Fin.cases ?_ ?_ i
  · rw [edge_zero]
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le _ (by simp)
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    decide
  · intro j
    rw [edge_succ]
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C, zero_add]
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le (by simp)
    simpa only [MvPolynomial.totalDegree_X] using
      (MvPolynomial.totalDegree_pow (X j.castSucc : MvPolynomial (Fin (k + 1)) ℤ) 2)

theorem error_degree (k : ℕ) : (errorPolynomial k).totalDegree ≤ 4 := by
  unfold errorPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (edge_degree k i))

theorem edge_weight (k : ℕ) (i : Fin (k + 1)) : weight (edge k i) ≤ 32 := by
  refine Fin.cases ?_ ?_ i
  · rw [edge_zero]
    have hsub := weight_sub (C 16 * X 0 : MvPolynomial (Fin (k + 1)) ℤ) 1
    have hmul := weight_mul_X (C 16 : MvPolynomial (Fin (k + 1)) ℤ) 0
    simp only [weight_one] at hsub
    rw [weight_C] at hmul
    change weight (C 16 * X 0 : MvPolynomial (Fin (k + 1)) ℤ) ≤ 16 at hmul
    omega
  · intro j
    rw [edge_succ]
    have hsub := weight_X_sub_sq j.succ j.castSucc
    have hmul := weight_mul (C 16 : MvPolynomial (Fin (k + 1)) ℤ) (X j.succ - X j.castSucc ^ 2)
    rw [weight_C] at hmul
    change weight (C 16 * (X j.succ - X j.castSucc ^ 2) : MvPolynomial (Fin (k + 1)) ℤ) ≤
      16 * weight (X j.succ - X j.castSucc ^ 2) at hmul
    omega

theorem error_weight (k : ℕ) : weight (errorPolynomial k) ≤ (k + 1) * 1024 := by
  classical
  have h (i : Fin (k + 1)) : weight (edge k i ^ 2) ≤ 1024 := by
    have hm := weight_mul (edge k i) (edge k i)
    have hb := Nat.mul_le_mul (edge_weight k i) (edge_weight k i)
    norm_num only at hb
    simpa only [← pow_two] using hm.trans hb
  unfold errorPolynomial weight
  calc
    _ ≤ ∑ i : Fin (k + 1), weight (edge k i ^ 2) := integerWeight.mvWeight_sum_le _ _
    _ ≤ ∑ _i : Fin (k + 1), 1024 := Finset.sum_le_sum (fun i _ => h i)
    _ = (k + 1) * 1024 := by simp

noncomputable def exactValues (k : ℕ) (i : Fin (k + 1)) : ℝ := exactChain (i.val + 1)

theorem exact_sequence (k i : ℕ) (hi : i ≤ k + 1) :
    sequence k (exactValues k) i = exactChain i := by
  cases i with
  | zero => rw [sequence_zero, exactChain_zero]
  | succ i =>
    have h := sequence_succ k (exactValues k) ⟨i, by omega⟩
    exact h

theorem exactValues_error_zero (k : ℕ) :
    (errorPolynomial k).eval₂ (Int.castRingHom ℝ) (exactValues k) = 0 := by
  simp only [errorPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_pow]
  apply Finset.sum_eq_zero
  intro i _
  rw [eval_edge, exact_sequence k (i.val + 1) (by omega), exact_sequence k i.val (by omega), exactChain_succ]
  ring

theorem exactValues_half_interior (k : ℕ) :
    ∀ i, -(1 / 2 : ℝ) < exactValues k i ∧ exactValues k i < 1 / 2 :=
  fun i => exactChain_in_half_cube (i.val + 1)

end JointThermoComplexity.Complexity.IntegerChainError

#print axioms JointThermoComplexity.Complexity.IntegerChainError.eval_errorPolynomial
#print axioms JointThermoComplexity.Complexity.IntegerChainError.terminal_square_bound
#print axioms JointThermoComplexity.Complexity.IntegerChainError.error_degree
#print axioms JointThermoComplexity.Complexity.IntegerChainError.error_weight
#print axioms JointThermoComplexity.Complexity.IntegerChainError.exactValues_error_zero
