module
public import proofs.JointThermoComplexity.Complexity.NaturalHeightBounds
public import proofs.JointThermoComplexity.Complexity.FixedQuarterSquaring

set_option autoImplicit false
@[expose] public section

/-! # Short exact quarter chains and strict thresholds from the height exponent -/

namespace JointThermoComplexity.Complexity.QuarterScaleSchedule
open NaturalHeightBounds FixedQuarterSquaring

theorem exactChain_tower_mul (m : ℕ) : exactChain m * (tower (m + 1) : ℝ) = 1 := by
  have hindex : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
  have hreal : (1 / 4 : ℝ) ^ (2 ^ m) * (2 : ℝ) ^ (2 ^ (m + 1)) = 1 := by
    rw [hindex, pow_mul, ← mul_pow]
    norm_num
  simpa only [exactChain, tower, Nat.cast_pow, Nat.cast_ofNat] using hreal

theorem half_tower_mul (k : ℕ) : (1 / 2 : ℝ) ^ (2 ^ k) * (tower k : ℝ) = 1 := by
  have hreal : (1 / 2 : ℝ) ^ (2 ^ k) * (2 : ℝ) ^ (2 ^ k) = 1 := by
    rw [← mul_pow]
    norm_num
  simpa only [tower, Nat.cast_pow, Nat.cast_ofNat] using hreal

theorem tower_monotone {a b : ℕ} (hab : a ≤ b) : tower a ≤ tower b :=
  Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) hab)

theorem quarter_scale_of_tower (H e m : ℕ) (hH : H + 1 ≤ tower e) (hm : e + 1 ≤ m) :
    exactChain m * ((H : ℝ) + 1) ≤ 1 / 4 := by
  have hbound : 4 * (H + 1) ≤ tower (m + 1) :=
    (Nat.mul_le_mul_left 4 hH).trans ((four_times_tower_le e).trans (tower_monotone (by omega)))
  have hreal : 4 * ((H : ℝ) + 1) ≤ (tower (m + 1) : ℝ) := by exact_mod_cast hbound
  have hmul := mul_le_mul_of_nonneg_left hreal (exactChain_pos m).le
  rw [exactChain_tower_mul] at hmul
  nlinarith only [hmul]

theorem half_threshold_lt_inverse (H e k : ℕ) (hH : H + 1 ≤ tower e) (hk : e + 1 ≤ k) :
    (1 / 2 : ℝ) ^ (2 ^ k) < 1 / ((H : ℝ) + 1) := by
  have hpos : 1 ≤ tower e := Nat.one_le_two_pow
  have hstrict : tower e < tower k :=
    (show tower e < 2 * tower e by omega).trans_le
      ((twice_tower_le e).trans (tower_monotone hk))
  have hreal : (H : ℝ) + 1 < (tower k : ℝ) := by exact_mod_cast hH.trans_lt hstrict
  have hpow : 0 < (1 / 2 : ℝ) ^ (2 ^ k) := pow_pos (by norm_num) _
  have hmul := mul_lt_mul_of_pos_left hreal hpow
  rw [half_tower_mul] at hmul
  exact (lt_div_iff₀ (by positivity : (0 : ℝ) < (H : ℝ) + 1)).mpr hmul

theorem quarter_scale_from_cap (n C B H m : ℕ) (hC : C ≤ 2 ^ B)
    (hH : H ≤ heightCap n C) (hm : heightExponent n B + 1 ≤ m) :
    exactChain m * ((H : ℝ) + 1) ≤ 1 / 4 :=
  quarter_scale_of_tower H (heightExponent n B) m
    ((Nat.add_le_add_right hH 1).trans (heightCap_add_one_bound n C B hC)) hm

theorem strict_threshold_from_cap (n C B H k : ℕ) (hC : C ≤ 2 ^ B)
    (hH : H ≤ heightCap n C) (hk : heightExponent n B + 1 ≤ k) :
    (1 / 2 : ℝ) ^ (2 ^ k) < 1 / ((H : ℝ) + 1) :=
  half_threshold_lt_inverse H (heightExponent n B) k
    ((Nat.add_le_add_right hH 1).trans (heightCap_add_one_bound n C B hC)) hk

end JointThermoComplexity.Complexity.QuarterScaleSchedule

#print axioms JointThermoComplexity.Complexity.QuarterScaleSchedule.quarter_scale_of_tower
#print axioms JointThermoComplexity.Complexity.QuarterScaleSchedule.half_threshold_lt_inverse
#print axioms JointThermoComplexity.Complexity.QuarterScaleSchedule.quarter_scale_from_cap
