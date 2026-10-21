module
public import proofs.JointThermoComplexity.Complexity.BitCodec
public import Mathlib.Tactic.NormNum

set_option autoImplicit false
@[expose] public section

/-! Fixed finite prefix lookup for the five signed literals of height at most two. -/

namespace JointThermoComplexity.Complexity.SmallIntegerLookup

def value : List Bool → ℤ
  | false :: true :: true :: false :: _ => 1
  | false :: true :: false :: true :: true :: false :: _ => 2
  | true :: true :: true :: false :: _ => -1
  | true :: true :: false :: true :: true :: false :: _ => -2
  | _ => 0

theorem value_bound (input : List Bool) : (value input).natAbs ≤ 2 := by
  unfold value
  split <;> norm_num

theorem value_code (z : ℤ) (hz : z.natAbs ≤ 2) (suffix : List Bool) : value (BitCodec.integerCode z ++ suffix) = z := by
  cases z with
  | ofNat k =>
    have hk : k ≤ 2 := by simpa only [Int.natAbs_ofNat'] using hz
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
        have he : k = 0 := by omega
        subst k
        rfl
  | negSucc k =>
    have hk : k ≤ 1 := by change k + 1 ≤ 2 at hz; omega
    cases k with
    | zero => rfl
    | succ k =>
      have he : k = 0 := by omega
      subst k
      rfl

theorem value_take (input : List Bool) : value (input.take 6) = value input := by
  cases input with
  | nil => rfl
  | cons a input =>
    cases input with
    | nil => cases a <;> rfl
    | cons b input =>
      cases input with
      | nil => cases a <;> cases b <;> rfl
      | cons c input =>
        cases input with
        | nil => cases a <;> cases b <;> cases c <;> rfl
        | cons d input =>
          cases input with
          | nil => cases a <;> cases b <;> cases c <;> cases d <;> rfl
          | cons e input =>
            cases input with
            | nil => cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl
            | cons f input => cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

end JointThermoComplexity.Complexity.SmallIntegerLookup

#print axioms JointThermoComplexity.Complexity.SmallIntegerLookup.value_code
#print axioms JointThermoComplexity.Complexity.SmallIntegerLookup.value_take
