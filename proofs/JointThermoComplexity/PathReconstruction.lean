module
public import proofs.JointThermoComplexity.WeightedPath
public import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity
open scoped BigOperators

/-- Literal path activities: v 0 is B and v n is the terminal complex A². -/
theorem reconstruct_path (n : ℕ) (w t : ℕ → ℝ) (q : ℝ)
    (hq : 0 < q) (hw : ∀ i < n, 0 < w i)
    (ht : ∀ i < n, 1/2 < t i ∧ t i < 1)
    (hsum : ∑ i ∈ Finset.range n, w i*t i = q) :
    ∃ B j : ℝ, ∃ v : ℕ → ℝ,
      (1/4 < B ∧ B < 1/2) ∧ j = 1/2-B ∧ 0 < j ∧
      v 0 = B ∧ v n = 1/4 ∧
      (∀ k ≤ n, 1/4 ≤ v k ∧ v k < 1/2) ∧
      (∀ i < n, (v i-v (i+1))/w i = j*t i) := by
  let B : ℝ := (1/4+q/2)/(1+q)
  let j : ℝ := 1/2-B
  have hd : 0 < 1+q := by linarith
  have hB : 1/4 < B ∧ B < 1/2 := by
    constructor
    · apply (lt_div_iff₀ hd).2; linarith
    · apply (div_lt_iff₀ hd).2; linarith
  have hj : 0 < j := by dsimp [j]; linarith [hB.2]
  have hrel : B-j*q=1/4 := by
    dsimp [B,j]
    field_simp
    ring
  let v : ℕ → ℝ := fun k => B-j*(∑ i ∈ Finset.range k, w i*t i)
  refine ⟨B,j,v,hB,rfl,hj,?_,?_,?_,?_⟩
  · simp [v]
  · simpa [v, hsum] using hrel
  · intro k hk
    have hnneg : ∀ i < n, 0 ≤ w i*t i := by
      intro i hi
      exact le_of_lt (mul_pos (hw i hi) (by linarith [(ht i hi).1]))
    have hnonneg : 0 ≤ ∑ i ∈ Finset.range k, w i*t i :=
      Finset.sum_nonneg (fun i hi => hnneg i (lt_of_lt_of_le (Finset.mem_range.mp hi) hk))
    have hle : (∑ i ∈ Finset.range k, w i*t i) ≤ q := by
      rw [← hsum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
        (fun i hi _ => hnneg i (Finset.mem_range.mp hi))
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hj)
    have hmul0 := mul_nonneg (le_of_lt hj) hnonneg
    dsimp [v]
    constructor <;> linarith [hB.2]
  · intro i hi
    have hwi : w i ≠ 0 := ne_of_gt (hw i hi)
    dsimp [v]
    rw [Finset.sum_range_succ]
    field_simp
    ring

theorem reconstructed_productions (n : ℕ) (j : ℝ)
    (hj : 0 < j) (t : Fin n → ℝ)
    (ht : ∀ i, 1/2 < t i ∧ t i < 1)
    (hdesc : ∀ i k, i < k → t k < t i) :
    (∀ i, 0 < 2*(j*t i)-j ∧ 0 < j-j*t i) ∧
    (∀ i k, i < k → 0 < j*t i-j*t k) := by
  constructor
  · intro i
    have hlo := mul_lt_mul_of_pos_left (ht i).1 hj
    have hhi := mul_lt_mul_of_pos_left (ht i).2 hj
    constructor <;> nlinarith
  · intro i k hik
    exact sub_pos.mpr (mul_lt_mul_of_pos_left (hdesc i k hik) hj)

end JointThermoComplexity



#print axioms JointThermoComplexity.reconstruct_path

#print axioms JointThermoComplexity.reconstructed_productions
