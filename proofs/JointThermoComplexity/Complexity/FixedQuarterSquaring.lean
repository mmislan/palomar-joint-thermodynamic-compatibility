module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

set_option autoImplicit false
@[expose] public section

/-! # Approximate repeated squaring from a fixed quarter

This is the fixed-start quantitative step used by the strict source reduction.
Its finite error budget follows the setting of Schaefer--Stefankovic, version6,
Lemma2.7. The proof below uses the rescaling z=(10/9)*y and natural powers,
so no logarithmic or real-power estimate is assumed.
-/

namespace JointThermoComplexity.Complexity.FixedQuarterSquaring

theorem trap_next (r a b : ℝ) (hr : 0 < r) (hrone : r ≤ 1) (ha : |a| < r / 2)
    (he : 20 * |b - a ^ 2| < r) : |b| < r / 2 := by
  have har := abs_nonneg a
  have hasq := sq_abs a
  have herr := abs_nonneg (b - a ^ 2)
  have hhi := le_abs_self (b - a ^ 2)
  have hlo := neg_le_abs (b - a ^ 2)
  have hrr : r ^ 2 ≤ r := by nlinarith only [hr, hrone]
  apply abs_lt.mpr
  constructor <;> nlinarith

theorem prefix_abs_lower (y : ℕ → ℝ) (m : ℕ) (hr : 0 < |y m|) (hrone : |y m| ≤ 1)
    (he : ∀ k < m, 20 * |y (k + 1) - y k ^ 2| < |y m|) :
    ∀ k ≤ m, |y m| / 2 ≤ |y k| := by
  have hback : ∀ d ≤ m, |y m| / 2 ≤ |y (m - d)| := by
    intro d
    induction d with
    | zero => intro _; simp only [Nat.sub_zero]; linarith only [hr]
    | succ d ih =>
      intro hd
      have hp := ih (by omega : d ≤ m)
      by_contra hsmall
      have hk : m - (d + 1) < m := by omega
      have htrap := trap_next (|y m|) (y (m - (d + 1)))
        (y (m - (d + 1) + 1)) hr hrone (lt_of_not_ge hsmall) (he _ hk)
      have hindex : m - (d + 1) + 1 = m - d := by omega
      rw [hindex] at htrap
      linarith only [hp, htrap]
  intro k hk
  have h := hback (m - k) (by omega)
  simpa only [Nat.sub_sub_self hk] using h

theorem prefix_pos (y : ℕ → ℝ) (m : ℕ) (hzero : y 0 = 1 / 4)
    (hr : 0 < |y m|) (hrone : |y m| ≤ 1)
    (he : ∀ k < m, 20 * |y (k + 1) - y k ^ 2| < |y m|) :
    ∀ k ≤ m, 0 < y k := by
  intro k hk
  cases k with
  | zero => rw [hzero]; norm_num
  | succ k =>
    have hlower := prefix_abs_lower y m hr hrone he (k + 1) hk
    have herr := he k (by omega)
    have habs := neg_le_abs (y (k + 1) - y k ^ 2)
    by_contra hn
    have hnonpos : y (k + 1) ≤ 0 := le_of_not_gt hn
    rw [abs_of_nonpos hnonpos] at hlower
    nlinarith only [hlower, herr, habs, sq_nonneg (y k), hr]

theorem rescaled_step (y : ℕ → ℝ) (m : ℕ) (hzero : y 0 = 1 / 4)
    (hr : 0 < |y m|) (hrone : |y m| ≤ 1)
    (he : ∀ k < m, 20 * |y (k + 1) - y k ^ 2| < |y m|) (k : ℕ) (hk : k < m) :
    (10 / 9 : ℝ) * y (k + 1) ≤ ((10 / 9 : ℝ) * y k) ^ 2 := by
  have hp := prefix_pos y m hzero hr hrone he (k + 1) (by omega)
  have hlower := prefix_abs_lower y m hr hrone he (k + 1) (by omega)
  rw [abs_of_pos hp] at hlower
  have herr := he k hk
  have habs := le_abs_self (y (k + 1) - y k ^ 2)
  nlinarith only [hlower, herr, habs]

theorem terminal_square_le (y : ℕ → ℝ) (m : ℕ) (hzero : y 0 = 1 / 4)
    (hr : 0 < |y m|) (hrone : |y m| ≤ 1)
    (he : ∀ k < m, 20 * |y (k + 1) - y k ^ 2| < |y m|) :
    0 < y m ^ 2 ∧ y m ^ 2 ≤ (1 / 2 : ℝ) ^ (2 ^ m) := by
  have hpos := prefix_pos y m hzero hr hrone he
  have hscaled : ∀ k ≤ m, (10 / 9 : ℝ) * y k ≤ (1 / 2 : ℝ) ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => intro _; rw [hzero]; norm_num
    | succ k ih =>
      intro hk
      have hp := ih (by omega : k ≤ m)
      have hstep := rescaled_step y m hzero hr hrone he k (by omega)
      have hnonneg : 0 ≤ (10 / 9 : ℝ) * y k := by linarith only [hpos k (by omega)]
      have hpow : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ k) := pow_nonneg (by norm_num) _
      have hsquare : ((10 / 9 : ℝ) * y k) ^ 2 ≤ ((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2 := by
        nlinarith only [hp, hnonneg, hpow]
      have hindex : ((1 / 2 : ℝ) ^ (2 ^ k)) ^ 2 = (1 / 2 : ℝ) ^ (2 ^ (k + 1)) := by
        rw [← pow_mul, pow_succ]
      exact hstep.trans (hsquare.trans_eq hindex)
  have hp := hpos m le_rfl
  have hs := hscaled m le_rfl
  have hmone : y m ≤ 1 := by simpa only [abs_of_pos hp] using hrone
  constructor
  · exact sq_pos_of_pos hp
  · nlinarith only [hp, hs, hmone]

def chainError (y : ℕ → ℝ) (m : ℕ) : ℝ := ∑ k ∈ Finset.range m, (y (k + 1) - y k ^ 2) ^ 2

theorem chainError_nonneg (y : ℕ → ℝ) (m : ℕ) : 0 ≤ chainError y m :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem terminal_square_le_of_sum (y : ℕ → ℝ) (m : ℕ) (hzero : y 0 = 1 / 4)
    (hrone : |y m| ≤ 1) (herr : 400 * chainError y m < y m ^ 2) :
    0 < y m ^ 2 ∧ y m ^ 2 ≤ (1 / 2 : ℝ) ^ (2 ^ m) := by
  have hspos : 0 < y m ^ 2 := by nlinarith only [herr, chainError_nonneg y m]
  have hr : 0 < |y m| := abs_pos.mpr (by intro hz; rw [hz] at hspos; norm_num at hspos)
  apply terminal_square_le y m hzero hr hrone
  intro k hk
  have hsingle : (y (k + 1) - y k ^ 2) ^ 2 ≤ chainError y m :=
    Finset.single_le_sum (f := fun j => (y (j + 1) - y j ^ 2) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_range.mpr hk)
  have ha := abs_nonneg (y (k + 1) - y k ^ 2)
  have hasq := sq_abs (y (k + 1) - y k ^ 2)
  have hrsq := sq_abs (y m)
  nlinarith

noncomputable def exactChain (k : ℕ) : ℝ := (1 / 4 : ℝ) ^ (2 ^ k)

@[simp] theorem exactChain_zero : exactChain 0 = 1 / 4 := by norm_num [exactChain]

theorem exactChain_succ (k : ℕ) : exactChain (k + 1) = exactChain k ^ 2 := by
  unfold exactChain
  rw [← pow_mul, pow_succ]

theorem exactChain_pos (k : ℕ) : 0 < exactChain k := pow_pos (by norm_num) _

theorem exactChain_le_quarter (k : ℕ) : exactChain k ≤ 1 / 4 := by
  induction k with
  | zero => rw [exactChain_zero]
  | succ k ih =>
    rw [exactChain_succ]
    nlinarith only [ih, exactChain_pos k]

theorem exactChain_in_half_cube (k : ℕ) : -(1 / 2 : ℝ) < exactChain k ∧ exactChain k < 1 / 2 := by
  have hp := exactChain_pos k
  have hq := exactChain_le_quarter k
  constructor <;> linarith only [hp, hq]

theorem exactChain_error_zero (m : ℕ) : chainError exactChain m = 0 := by
  unfold chainError
  apply Finset.sum_eq_zero
  intro k _
  rw [exactChain_succ]
  ring

theorem exactChain_strict_budget (m : ℕ) : 400 * chainError exactChain m < exactChain m ^ 2 := by
  rw [exactChain_error_zero, mul_zero]
  exact sq_pos_of_pos (exactChain_pos m)

end JointThermoComplexity.Complexity.FixedQuarterSquaring

#print axioms JointThermoComplexity.Complexity.FixedQuarterSquaring.terminal_square_le
#print axioms JointThermoComplexity.Complexity.FixedQuarterSquaring.terminal_square_le_of_sum
#print axioms JointThermoComplexity.Complexity.FixedQuarterSquaring.exactChain_in_half_cube
#print axioms JointThermoComplexity.Complexity.FixedQuarterSquaring.exactChain_strict_budget
