module
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring

set_option autoImplicit false
@[expose] public section

/-! # Polynomial exponents for explicit factorial elimination heights

The factorial/power rearrangement adapts the proof pattern in the private
D-stability QuadraticHeightSchedule.lean. Its exact source snapshot and license
are recorded in HEIGHT_SCHEDULE_PATTERN_PROVENANCE.json. These lemmas are
freshly checked statements using an explicit binary coefficient exponent B;
no foreign receipt or source-hardness premise is used as a theorem.
-/

namespace JointThermoComplexity.Complexity.NaturalHeightBounds

def tower (e : ℕ) : ℕ := 2 ^ (2 ^ e)

def heightCap (n C : ℕ) : ℕ :=
  (5 ^ n).factorial * (2 * C ^ (4 * n + 5)) ^ (5 ^ n)

def heightExponent (n B : ℕ) : ℕ := 6 * n + B * (4 * n + 5) + 2

theorem twice_tower_le (e : ℕ) : 2 * tower e ≤ tower (e + 1) := by
  have he : 2 ^ e + 1 ≤ 2 ^ (e + 1) := by
    rw [pow_succ]
    have hone : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    omega
  calc
    2 * tower e = 2 ^ (2 ^ e + 1) := by rw [tower, pow_succ]; omega
    _ ≤ tower (e + 1) := Nat.pow_le_pow_right (by decide) he

theorem four_times_tower_le (e : ℕ) : 4 * tower e ≤ tower (e + 2) := by
  calc
    4 * tower e = 2 * (2 * tower e) := by omega
    _ ≤ 2 * tower (e + 1) := Nat.mul_le_mul_left 2 (twice_tower_le e)
    _ ≤ tower (e + 2) := twice_tower_le (e + 1)

theorem heightCap_bound (n C B : ℕ) (hC : C ≤ 2 ^ B) :
    heightCap n C ≤ tower (6 * n + B * (4 * n + 5) + 1) := by
  let M := 5 ^ n
  let A := 1 + 3 * n + B * (4 * n + 5)
  have hM : M ≤ 2 ^ (3 * n) := by
    calc
      M ≤ 8 ^ n := Nat.pow_le_pow_left (by decide : 5 ≤ 8) n
      _ = 2 ^ (3 * n) := by rw [show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_mul]
  have hbase : 2 * M * C ^ (4 * n + 5) ≤ 2 ^ A := by
    calc
      _ ≤ 2 * 2 ^ (3 * n) * (2 ^ B) ^ (4 * n + 5) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hM) (Nat.pow_le_pow_left hC _)
      _ = 2 ^ A := by dsimp [A]; simp only [pow_add, pow_mul, pow_one]
  have hexp : A * M ≤ 2 ^ (A + 3 * n) := by
    calc
      _ ≤ 2 ^ A * 2 ^ (3 * n) := Nat.mul_le_mul (Nat.lt_two_pow_self : A < 2 ^ A).le hM
      _ = _ := (pow_add _ _ _).symm
  have he : A + 3 * n = 6 * n + B * (4 * n + 5) + 1 := by dsimp [A]; omega
  calc
    heightCap n C ≤ M ^ M * (2 * C ^ (4 * n + 5)) ^ M :=
      Nat.mul_le_mul_right _ (Nat.factorial_le_pow M)
    _ = (2 * M * C ^ (4 * n + 5)) ^ M := by rw [← mul_pow]; congr 1; ring
    _ ≤ (2 ^ A) ^ M := Nat.pow_le_pow_left hbase _
    _ = 2 ^ (A * M) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (2 ^ (A + 3 * n)) := Nat.pow_le_pow_right (by decide) hexp
    _ = tower (6 * n + B * (4 * n + 5) + 1) := by rw [he]; rfl

theorem heightCap_add_one_bound (n C B : ℕ) (hC : C ≤ 2 ^ B) :
    heightCap n C + 1 ≤ tower (heightExponent n B) := by
  let e := 6 * n + B * (4 * n + 5) + 1
  have h := heightCap_bound n C B hC
  have hone : 1 ≤ tower e := Nat.one_le_two_pow
  have hsum : heightCap n C + 1 ≤ 2 * tower e := by change heightCap n C ≤ tower e at h; omega
  have he : e + 1 = heightExponent n B := by rfl
  exact hsum.trans (by simpa only [he] using twice_tower_le e)

theorem witness_form_le_cap (n C : ℕ) (hC : 1 ≤ C) :
    (5 ^ n).factorial * (2 * C ^ (4 * n + 1)) ^ (5 ^ n) ≤ heightCap n C := by
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right hC (by omega : 4 * n + 1 ≤ 4 * n + 5))) _)

theorem minimum_form_le_cap (n C G : ℕ) (hGC : G + 1 ≤ C) :
    (5 ^ n).factorial * ((G + 1) * C ^ (4 * n + 4)) ^ (5 ^ n) ≤ heightCap n C := by
  have hbase : (G + 1) * C ^ (4 * n + 4) ≤ 2 * C ^ (4 * n + 5) := by
    calc
      _ ≤ C * C ^ (4 * n + 4) := Nat.mul_le_mul_right _ hGC
      _ = C ^ (4 * n + 5) := by rw [show 4 * n + 5 = (4 * n + 4) + 1 by omega, pow_succ]; ring
      _ ≤ _ := by omega
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)

theorem critical_length_power_bound (G M W a b : ℕ)
    (hG : G ≤ M * W ^ 2) (hM : M ≤ 2 ^ a) (hW : W ≤ 2 ^ b) :
    6 + 4 * G ≤ 2 ^ (a + 2 * b + 4) := by
  have hpow : 2 ^ a * (2 ^ b) ^ 2 = 2 ^ (a + 2 * b) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hg : G ≤ 2 ^ (a + 2 * b) :=
    hG.trans ((Nat.mul_le_mul hM (Nat.pow_le_pow_left hW 2)).trans_eq hpow)
  have hone : 1 ≤ 2 ^ (a + 2 * b) := Nat.one_le_two_pow
  have hfour : 2 ^ (a + 2 * b + 4) = 16 * 2 ^ (a + 2 * b) := by rw [pow_add]; ring
  rw [hfour]
  omega

end JointThermoComplexity.Complexity.NaturalHeightBounds

#print axioms JointThermoComplexity.Complexity.NaturalHeightBounds.heightCap_add_one_bound
#print axioms JointThermoComplexity.Complexity.NaturalHeightBounds.minimum_form_le_cap
#print axioms JointThermoComplexity.Complexity.NaturalHeightBounds.critical_length_power_bound
