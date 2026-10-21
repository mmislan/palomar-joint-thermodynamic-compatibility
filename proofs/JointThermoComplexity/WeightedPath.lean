module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity
open scoped BigOperators

/-- A weighted mean can realize every strict value while its entries strictly descend. -/
theorem weighted_chain_exists (n : ℕ) (hn : 0 < n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (q : ℝ)
    (hqlo : (∑ i, w i)/2 < q) (hqhi : q < ∑ i, w i) :
    ∃ t : Fin n → ℝ,
      (∀ i, 1/2 < t i ∧ t i < 1) ∧
      (∀ i j, i < j → t j < t i) ∧ (∑ i, w i * t i) = q := by
  let R := ∑ i, w i
  have hR : 0 < R := Finset.sum_pos (fun i _ => hw i)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  let θ := q/R
  have hθlo : 1/2 < θ := (lt_div_iff₀ hR).2 (by dsimp [R] at *; linarith)
  have hθhi : θ < 1 := (div_lt_iff₀ hR).2 (by simpa [R] using hqhi)
  let c : Fin n → ℝ := fun i => -(i.val : ℝ)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hc (i : Fin n) : -(n:ℝ) ≤ c i ∧ c i ≤ 0 := by
    have hi : (i.val:ℝ) < n := by exact_mod_cast i.isLt
    have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
    dsimp [c]
    constructor <;> linarith
  let μ := (∑ i, w i*c i)/R
  have hμlo : -(n:ℝ) ≤ μ := by
    apply (le_div_iff₀ hR).2
    calc
      -(n:ℝ)*R = ∑ i, w i * (-(n:ℝ)) := by rw [← Finset.sum_mul]; ring
      _ ≤ ∑ i, w i*c i := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hc i).1 (le_of_lt (hw i)))
  have hμhi : μ ≤ 0 := by
    apply (div_le_iff₀ hR).2
    simpa using Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hw i)) (hc i).2)
  let δ := min (θ-1/2) (1-θ)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδlo : δ ≤ θ-1/2 := min_le_left _ _
  have hδhi : δ ≤ 1-θ := min_le_right _ _
  let ε := δ/(2*((n:ℝ)+1))
  have hden : 0 < 2*((n:ℝ)+1) := by positivity
  have hε : 0 < ε := div_pos hδ hden
  have heq : ε*(2*((n:ℝ)+1))=δ := div_mul_cancel₀ _ (ne_of_gt hden)
  have hsmall : ε*(n:ℝ) < δ := by nlinarith
  let t : Fin n → ℝ := fun i => θ+ε*(c i-μ)
  refine ⟨t, ?_, ?_, ?_⟩
  · intro i
    have hl : -(n:ℝ) ≤ c i-μ := by linarith [(hc i).1]
    have hu : c i-μ ≤ (n:ℝ) := by linarith [(hc i).2]
    have hl' := mul_le_mul_of_nonneg_left hl (le_of_lt hε)
    have hu' := mul_le_mul_of_nonneg_left hu (le_of_lt hε)
    dsimp [t]
    constructor <;> nlinarith
  · intro i j hij
    have hij' : (i.val:ℝ) < j.val := by exact_mod_cast hij
    dsimp [t, c]
    nlinarith
  · have hμR : μ*R = ∑ i, w i*c i := div_mul_cancel₀ _ (ne_of_gt hR)
    have hθR : θ*R=q := div_mul_cancel₀ _ (ne_of_gt hR)
    calc
      (∑ i, w i*t i) = θ*R+ε*((∑ i, w i*c i)-μ*R) := by
        calc
          _ = ∑ i, (θ*w i + ε*(w i*c i) - (ε*μ)*w i) := by
            apply Finset.sum_congr rfl
            intro i _
            dsimp [t]
            ring
          _ = _ := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
            dsimp [R]
            ring
      _ = q := by rw [hμR, sub_self, mul_zero, add_zero, hθR]

theorem weighted_chain_necessary {n : ℕ} (hn : 0 < n) (w t : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (ht : ∀ i, 1/2 < t i ∧ t i < 1) :
    (∑ i, w i)/2 < ∑ i, w i*t i ∧ (∑ i, w i*t i) < ∑ i, w i := by
  have hlo := Finset.sum_lt_sum_of_nonempty
    (s := (Finset.univ : Finset (Fin n))) ⟨⟨0,hn⟩, Finset.mem_univ _⟩
    (fun i _ => mul_lt_mul_of_pos_left (ht i).1 (hw i))
  have hhi := Finset.sum_lt_sum_of_nonempty
    (s := (Finset.univ : Finset (Fin n))) ⟨⟨0,hn⟩, Finset.mem_univ _⟩
    (fun i _ => mul_lt_mul_of_pos_left (ht i).2 (hw i))
  constructor
  · simpa [← Finset.sum_mul, div_eq_mul_inv] using hlo
  · simpa using hhi

end JointThermoComplexity

#print axioms JointThermoComplexity.weighted_chain_exists

#print axioms JointThermoComplexity.weighted_chain_necessary
