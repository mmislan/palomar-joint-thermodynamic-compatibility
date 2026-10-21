module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

set_option autoImplicit false
@[expose] public section

/-! Positive natural denominators chosen from the input integer coefficient.
The right factor is2 divided by its denominator, matching a halved branch
coefficient. No activity or satisfiability witness occurs in these data. -/

namespace JointThermoComplexity.Complexity.RationalBranchCoefficients

def leftDenominator (c : ℤ) : ℕ := c.natAbs + 1
def rightDenominator (c : ℤ) : ℕ := 2 * c.toNat + 1

theorem left_pos (c : ℤ) : 0 < leftDenominator c := by unfold leftDenominator; omega
theorem right_pos (c : ℤ) : 0 < rightDenominator c := by unfold rightDenominator; omega
theorem left_one_le (c : ℤ) : 1 ≤ leftDenominator c := left_pos c
theorem right_one_le (c : ℤ) : 1 ≤ rightDenominator c := right_pos c

theorem left_real (c : ℤ) : (leftDenominator c : ℝ) = |(c : ℝ)| + 1 := by
  simp only [leftDenominator, Nat.cast_add, Nat.cast_one, Nat.cast_natAbs, Int.cast_abs]

theorem right_int (c : ℤ) : (rightDenominator c : ℤ) = c + |c| + 1 := by
  simp only [rightDenominator, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Int.toNat_eq_max]
  by_cases hc : 0 ≤ c
  · rw [max_eq_left hc, abs_of_nonneg hc]
    ring
  · have hn : c ≤ 0 := le_of_not_ge hc
    rw [max_eq_right hn, abs_of_nonpos hn]
    ring

theorem right_real (c : ℤ) : (rightDenominator c : ℝ) = (c : ℝ) + |(c : ℝ)| + 1 := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (right_int c)
  simpa only [Int.cast_natCast, Int.cast_add, Int.cast_abs, Int.cast_one] using h

theorem left_bound {C : ℕ} (c : ℤ) (hc : c.natAbs ≤ C) : leftDenominator c ≤ C + 1 := by
  unfold leftDenominator
  omega

theorem right_bound {C : ℕ} (c : ℤ) (hc : c.natAbs ≤ C) : rightDenominator c ≤ 2 * C + 1 := by
  have h := Int.toNat_add_toNat_neg_eq_natAbs c
  unfold rightDenominator
  omega

theorem left_factor (c : ℤ) : (1 : ℝ) / leftDenominator c = 1 / (|(c : ℝ)| + 1) := by rw [left_real]
theorem right_factor (c : ℤ) : (2 : ℝ) / rightDenominator c = 1 / (((c : ℝ) + |(c : ℝ)| + 1) / 2) := by
  rw [← right_real, one_div_div]

theorem left_factor_bounds (c : ℤ) : 0 < (1 : ℝ) / leftDenominator c ∧ (1 : ℝ) / leftDenominator c ≤ 2 := by
  have h : (1 : ℝ) ≤ leftDenominator c := by exact_mod_cast left_one_le c
  have hp : (0 : ℝ) < leftDenominator c := lt_of_lt_of_le zero_lt_one h
  exact ⟨div_pos zero_lt_one hp, (div_le_iff₀ hp).mpr (by linarith)⟩

theorem right_factor_bounds (c : ℤ) : 0 < (2 : ℝ) / rightDenominator c ∧ (2 : ℝ) / rightDenominator c ≤ 2 := by
  have h : (1 : ℝ) ≤ rightDenominator c := by exact_mod_cast right_one_le c
  have hp : (0 : ℝ) < rightDenominator c := lt_of_lt_of_le zero_lt_one h
  exact ⟨div_pos (by norm_num) hp, (div_le_iff₀ hp).mpr (by linarith)⟩

end JointThermoComplexity.Complexity.RationalBranchCoefficients

#print axioms JointThermoComplexity.Complexity.RationalBranchCoefficients.leftDenominator
#print axioms JointThermoComplexity.Complexity.RationalBranchCoefficients.rightDenominator
#print axioms JointThermoComplexity.Complexity.RationalBranchCoefficients.right_real
#print axioms JointThermoComplexity.Complexity.RationalBranchCoefficients.left_factor_bounds
#print axioms JointThermoComplexity.Complexity.RationalBranchCoefficients.right_factor_bounds
