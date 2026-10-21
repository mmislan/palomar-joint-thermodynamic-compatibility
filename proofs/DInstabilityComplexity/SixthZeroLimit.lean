module
public import proofs.DInstabilityComplexity.CoerciveSixthMinimum

@[expose] public section

/-! # A common vector limit of regularized minima is an exact zero

The original zero witness is used only to supply an unknown compact box.
The same limiting vector will later receive every coordinate eliminant bound.
-/

namespace DInstabilityComplexity.Separation

open Filter
open scoped Topology

noncomputable section

variable {ι : Type*} [Fintype ι]

def zeroLimitParameter (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem zeroLimitParameter_pos (n : ℕ) : 0 < zeroLimitParameter n := by
  unfold zeroLimitParameter
  positivity

theorem zeroLimitParameter_tendsto : Tendsto zeroLimitParameter atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0)
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))

theorem sixth_localMin_of_global (S : (ι → ℝ) → ℝ) (ε : ℝ) (x : ι → ℝ)
    (hx : ∀ y, sixthObjective S ε x ≤ sixthObjective S ε y) :
    IsLocalMin (sixthObjective S ε) x := by
  have hm : IsMinOn (sixthObjective S ε) Set.univ x :=
    isMinOn_iff.mpr (fun y _ => hx y)
  exact hm.isLocalMin (by simp)

theorem exists_sixth_zero_limit (S : (ι → ℝ) → ℝ) (hS : Continuous S)
    (hn : ∀ x, 0 ≤ S x) (w : ι → ℝ) (hw : S w = 0) :
    ∃ x₀ : ι → ℝ, ∃ z : ℕ → ι → ℝ, ∃ t : ℕ → ℝ,
      Tendsto z atTop (𝓝 x₀) ∧ Tendsto t atTop (𝓝 0) ∧
        (∀ n, 0 < t n) ∧ (∀ n, IsLocalMin (sixthObjective S (t n)) (z n)) ∧ S x₀ = 0 := by
  classical
  choose xs hmin using fun n => exists_sixth_global_minimizer S hS hn
    (zeroLimitParameter n) (zeroLimitParameter_pos n)
  have hcomp (n : ℕ) := sixth_minimizer_zero_comparison S hn (zeroLimitParameter n)
    (zeroLimitParameter_pos n) (xs n) w (hmin n) hw
  let R := finiteSixthSum w + 1
  have hbox (n : ℕ) : xs n ∈ realCoordinateBox R := by
    intro i _
    apply abs_le.mp
    exact (coordinate_abs_le_sixthSum_add_one (xs n) i).trans
      (add_le_add (hcomp n).2 (le_refl (1 : ℝ)))
  have hupperlim : Tendsto (fun n => zeroLimitParameter n * finiteSixthSum w)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using zeroLimitParameter_tendsto.mul_const (finiteSixthSum w)
  have hSlim : Tendsto (fun n => S (xs n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => hn (xs n)) (fun n => (hcomp n).1) hupperlim
  obtain ⟨x₀, _, φ, hφ, hxlim⟩ := (isCompact_realCoordinateBox (ι := ι) R).tendsto_subseq hbox
  have hφlim : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hSactual : Tendsto (fun n => S (xs (φ n))) atTop (𝓝 (S x₀)) := by
    convert hS.continuousAt.tendsto.comp hxlim using 1
    ext n
    rfl
  have hSzero : Tendsto (fun n => S (xs (φ n))) atTop (𝓝 0) := hSlim.comp hφlim
  refine ⟨x₀, xs ∘ φ, zeroLimitParameter ∘ φ, hxlim,
    zeroLimitParameter_tendsto.comp hφlim, fun n => zeroLimitParameter_pos (φ n), ?_,
    tendsto_nhds_unique hSactual hSzero⟩
  intro n
  exact sixth_localMin_of_global S (zeroLimitParameter (φ n)) (xs (φ n)) (hmin (φ n))

#print axioms zeroLimitParameter_tendsto
#print axioms exists_sixth_zero_limit

end
end DInstabilityComplexity.Separation
