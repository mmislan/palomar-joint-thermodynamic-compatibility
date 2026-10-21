module
public import Mathlib

@[expose] public section

/-! # Global minima supplied by a positive sixth-power regularizer

The radius is proved from the objective at zero. No minimizing-point or
coercivity certificate is assumed. Empty finite coordinate types are allowed.
-/

namespace DInstabilityComplexity.Separation

noncomputable section

variable {ι : Type*} [Fintype ι]

def finiteSixthSum (x : ι → ℝ) : ℝ := ∑ i, x i ^ 6

def sixthObjective (S : (ι → ℝ) → ℝ) (ε : ℝ) (x : ι → ℝ) : ℝ :=
  S x + ε * finiteSixthSum x

def realCoordinateBox (R : ℝ) : Set (ι → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-R) R)

theorem finiteSixthSum_nonneg (x : ι → ℝ) : 0 ≤ finiteSixthSum x :=
  Finset.sum_nonneg (fun _ _ => by positivity)

theorem finiteSixthSum_single_le (x : ι → ℝ) (i : ι) : x i ^ 6 ≤ finiteSixthSum x := by
  classical
  unfold finiteSixthSum
  exact Finset.single_le_sum (f := fun j => x j ^ 6)
    (fun _ _ => by positivity) (Finset.mem_univ i)

theorem finiteSixthSum_zero : finiteSixthSum (0 : ι → ℝ) = 0 := by simp [finiteSixthSum]

theorem continuous_finiteSixthSum : Continuous (finiteSixthSum (ι := ι)) := by
  unfold finiteSixthSum
  fun_prop

theorem continuous_sixthObjective (S : (ι → ℝ) → ℝ) (hS : Continuous S) (ε : ℝ) :
    Continuous (sixthObjective S ε) :=
  hS.add (continuous_finiteSixthSum.const_mul ε)

omit [Fintype ι] in
theorem isCompact_realCoordinateBox (R : ℝ) : IsCompact (realCoordinateBox (ι := ι) R) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

omit [Fintype ι] in
theorem zero_mem_realCoordinateBox {R : ℝ} (hR : 0 ≤ R) :
    (0 : ι → ℝ) ∈ realCoordinateBox R := by
  intro i _
  change -R ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ R
  exact ⟨neg_nonpos.mpr hR, hR⟩

theorem abs_le_sixthPower_of_one_le {u : ℝ} (hu : 1 ≤ |u|) : |u| ≤ u ^ 6 := by
  calc
    |u| ≤ |u| ^ 6 := le_self_pow₀ hu (by decide)
    _ = u ^ 6 := by rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ u ^ 6)]

theorem exists_sixth_global_minimizer (S : (ι → ℝ) → ℝ) (hS : Continuous S)
    (hn : ∀ x, 0 ≤ S x) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : ι → ℝ, ∀ y, sixthObjective S ε x ≤ sixthObjective S ε y := by
  classical
  let R : ℝ := 1 + (S 0 + 1) / ε
  have hdiv : 0 < (S 0 + 1) / ε := div_pos (by linarith only [hn 0]) hε
  have hR : 1 < R := by dsimp only [R]; linarith only [hdiv]
  have hR₀ : 0 ≤ R := le_trans (by norm_num) hR.le
  have hcancel : ε * ((S 0 + 1) / ε) = S 0 + 1 := by
    calc
      _ = ((S 0 + 1) / ε) * ε := mul_comm _ _
      _ = S 0 + 1 := div_mul_cancel₀ _ (ne_of_gt hε)
  have hsmall : S 0 < ε * R := by
    dsimp only [R]
    rw [mul_add, mul_one, hcancel]
    linarith only [hε]
  obtain ⟨x, _, hmin⟩ := (isCompact_realCoordinateBox (ι := ι) R).exists_isMinOn
    ⟨0, zero_mem_realCoordinateBox hR₀⟩ (continuous_sixthObjective S hS ε).continuousOn
  have hx0 := (isMinOn_iff.mp hmin) 0 (zero_mem_realCoordinateBox hR₀)
  have hx : S x + ε * finiteSixthSum x ≤ S 0 := by
    simpa only [sixthObjective, finiteSixthSum_zero, mul_zero, add_zero] using hx0
  refine ⟨x, ?_⟩
  intro y
  by_cases hy : y ∈ realCoordinateBox R
  · exact (isMinOn_iff.mp hmin) y hy
  · have hex : ∃ i, R < |y i| := by
      by_contra! hle
      apply hy
      intro i _
      exact abs_le.mp (hle i)
    obtain ⟨i, hi⟩ := hex
    have hpow := abs_le_sixthPower_of_one_le (hR.le.trans hi.le)
    have hsum : R < finiteSixthSum y := hi.trans_le (hpow.trans (finiteSixthSum_single_le y i))
    have hreg : ε * R < ε * finiteSixthSum y := mul_lt_mul_of_pos_left hsum hε
    change S x + ε * finiteSixthSum x ≤ S y + ε * finiteSixthSum y
    linarith only [hx, hn y, hsmall, hreg]

theorem sixth_minimizer_zero_comparison (S : (ι → ℝ) → ℝ) (hn : ∀ x, 0 ≤ S x)
    (ε : ℝ) (hε : 0 < ε) (x w : ι → ℝ)
    (hmin : ∀ y, sixthObjective S ε x ≤ sixthObjective S ε y) (hw : S w = 0) :
    S x ≤ ε * finiteSixthSum w ∧ finiteSixthSum x ≤ finiteSixthSum w := by
  have hm := hmin w
  change S x + ε * finiteSixthSum x ≤ S w + ε * finiteSixthSum w at hm
  rw [hw, zero_add] at hm
  have hx := hn x
  have hreg := mul_nonneg hε.le (finiteSixthSum_nonneg x)
  constructor
  · linarith only [hm, hreg]
  · apply (mul_le_mul_iff_right₀ hε).mp
    linarith only [hm, hx]

theorem coordinate_abs_le_sixthSum_add_one (x : ι → ℝ) (i : ι) :
    |x i| ≤ finiteSixthSum x + 1 := by
  by_cases hi : |x i| ≤ 1
  · have hn := finiteSixthSum_nonneg x
    linarith only [hi, hn]
  · have hp := abs_le_sixthPower_of_one_le (le_of_not_ge hi)
    have hh := hp.trans (finiteSixthSum_single_le x i)
    linarith only [hh]

#print axioms exists_sixth_global_minimizer
#print axioms sixth_minimizer_zero_comparison
#print axioms coordinate_abs_le_sixthSum_add_one

end
end DInstabilityComplexity.Separation
