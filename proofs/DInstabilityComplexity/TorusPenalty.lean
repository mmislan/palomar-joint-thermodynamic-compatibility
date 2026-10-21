module
public import proofs.DInstabilityComplexity.TorusPolynomial
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Tactic.FunProp

@[expose] public section

/-!
# Interior minimizers for a pure-power deformation

The sixth-power term produces pure fifth powers in the gradient equations.
Minimizing on a fixed compact box avoids a coercivity hypothesis; the penalty
excludes its boundary at the explicit small parameter scale below.
-/

namespace DInstabilityComplexity.Separation

noncomputable section

def circleDefect (x : TorusCoords k → ℝ) (e : Fin k) : ℝ :=
  x (e, false) ^ 2 + x (e, true) ^ 2 - 1

def torusPenalty (x : TorusCoords k → ℝ) : ℝ := ∑ e, circleDefect x e ^ 2

def torusEnergy (M : Matrix (Fin r) (Fin k) ℤ) (x : TorusCoords k → ℝ) : ℝ :=
  ∑ c, ((∑ e, (M c e : ℝ) * x (e, false)) ^ 2 +
    (∑ e, (M c e : ℝ) * x (e, true)) ^ 2)

def sixthRegularizer (x : TorusCoords k → ℝ) : ℝ := ∑ i, x i ^ 6

def perturbedEnergy (M : Matrix (Fin r) (Fin k) ℤ) (t : ℝ)
    (x : TorusCoords k → ℝ) : ℝ :=
  torusPenalty x + t * torusEnergy M x + t ^ 2 * sixthRegularizer x

def referenceCoords (k : ℕ) : TorusCoords k → ℝ := fun p => if p.2 then 0 else 1

def torusBox (k : ℕ) : Set (TorusCoords k → ℝ) :=
  Set.pi Set.univ fun _ => Set.Icc (-2) 2

theorem torusPenalty_nonneg (x : TorusCoords k → ℝ) : 0 ≤ torusPenalty x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem torusEnergy_nonneg (M : Matrix (Fin r) (Fin k) ℤ) (x : TorusCoords k → ℝ) :
    0 ≤ torusEnergy M x := Finset.sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem sixthRegularizer_nonneg (x : TorusCoords k → ℝ) : 0 ≤ sixthRegularizer x :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem torusPenalty_eq_zero_iff (x : TorusCoords k → ℝ) :
    torusPenalty x = 0 ↔ ∀ e, x (e, false) ^ 2 + x (e, true) ^ 2 = 1 := by
  simp only [torusPenalty, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _),
    Finset.mem_univ, forall_const, sq_eq_zero_iff, circleDefect, sub_eq_zero]

theorem reference_penalty (k : ℕ) : torusPenalty (referenceCoords k) = 0 := by
  simp [torusPenalty, circleDefect, referenceCoords]

theorem reference_regularizer (k : ℕ) : sixthRegularizer (referenceCoords k) = k := by
  simp [sixthRegularizer, referenceCoords, Fintype.sum_prod_type]

theorem reference_mem_box (k : ℕ) : referenceCoords k ∈ torusBox k := by
  rintro ⟨e, b⟩ _
  cases b <;> norm_num [referenceCoords]

theorem isCompact_torusBox (k : ℕ) : IsCompact (torusBox k) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem continuous_torusPenalty (k : ℕ) : Continuous (torusPenalty (k := k)) := by
  unfold torusPenalty circleDefect
  fun_prop

theorem continuous_torusEnergy (M : Matrix (Fin r) (Fin k) ℤ) : Continuous (torusEnergy M) := by
  unfold torusEnergy
  fun_prop

theorem continuous_sixthRegularizer (k : ℕ) : Continuous (sixthRegularizer (k := k)) := by
  unfold sixthRegularizer
  fun_prop

theorem continuous_perturbedEnergy (M : Matrix (Fin r) (Fin k) ℤ) (t : ℝ) :
    Continuous (perturbedEnergy M t) := by
  exact ((continuous_torusPenalty k).add ((continuous_torusEnergy M).const_mul t)).add
    ((continuous_sixthRegularizer k).const_mul (t ^ 2))

theorem exists_box_minimizer (M : Matrix (Fin r) (Fin k) ℤ) (t : ℝ) :
    ∃ x ∈ torusBox k, IsMinOn (perturbedEnergy M t) (torusBox k) x :=
  (isCompact_torusBox k).exists_isMinOn ⟨referenceCoords k, reference_mem_box k⟩
    (continuous_perturbedEnergy M t).continuousOn

theorem penalty_le_perturbedEnergy (M : Matrix (Fin r) (Fin k) ℤ) (t : ℝ)
    (ht : 0 ≤ t) (x : TorusCoords k → ℝ) : torusPenalty x ≤ perturbedEnergy M t x := by
  have hE := mul_nonneg ht (torusEnergy_nonneg M x)
  have hR := mul_nonneg (sq_nonneg t) (sixthRegularizer_nonneg x)
  unfold perturbedEnergy
  linarith

/-- Any coordinate outside the open box forces a fixed penalty of at least 9. -/
theorem penalty_ge_nine (x : TorusCoords k → ℝ) (i : TorusCoords k)
    (hi : 2 ≤ |x i|) : 9 ≤ torusPenalty x := by
  have hsq : 4 ≤ x i ^ 2 := by nlinarith [sq_abs (x i)]
  have hdef : 3 ≤ circleDefect x i.1 := by
    obtain ⟨e, b⟩ := i
    cases b <;> simp only [circleDefect] at * <;> nlinarith [sq_nonneg (x (e, false)), sq_nonneg (x (e, true))]
  have hle : circleDefect x i.1 ^ 2 ≤ torusPenalty x :=
    Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i.1)
  nlinarith

theorem perturbed_reference_lt_one (M : Matrix (Fin r) (Fin k) ℤ) (t : ℝ)
    (ht : 0 < t) (hscale : t * (torusEnergy M (referenceCoords k) + k + 1) ≤ 1) :
    perturbedEnergy M t (referenceCoords k) < 1 := by
  have hE := torusEnergy_nonneg M (referenceCoords k)
  have hk : (0 : ℝ) ≤ k := by positivity
  have htone : t ≤ 1 := by nlinarith
  have hpow : t ^ 2 ≤ t := by nlinarith
  have htk := mul_le_mul_of_nonneg_right hpow hk
  simp only [perturbedEnergy, reference_penalty, reference_regularizer, zero_add]
  nlinarith

/-- Every small-parameter box minimizer is an unconstrained interior point. -/
theorem box_minimizer_interior (M : Matrix (Fin r) (Fin k) ℤ) (t : ℝ)
    (ht : 0 < t) (hscale : t * (torusEnergy M (referenceCoords k) + k + 1) ≤ 1)
    (x : TorusCoords k → ℝ) (hx : IsMinOn (perturbedEnergy M t) (torusBox k) x) :
    ∀ i, |x i| < 2 := by
  intro i
  by_contra hi
  have hpen := penalty_ge_nine x i (le_of_not_gt hi)
  have hle := penalty_le_perturbedEnergy M t ht.le x
  have hmin := (isMinOn_iff.mp hx) _ (reference_mem_box k)
  have hsmall := perturbed_reference_lt_one M t ht hscale
  linarith

/-- Comparison against any exact torus point controls the objective itself. -/
theorem energy_bound_at_minimizer (M : Matrix (Fin r) (Fin k) ℤ) (t : ℝ)
    (ht : 0 < t) (x y : TorusCoords k → ℝ)
    (hmin : perturbedEnergy M t x ≤ perturbedEnergy M t y)
    (hy : torusPenalty y = 0) :
    torusEnergy M x ≤ torusEnergy M y + t * sixthRegularizer y := by
  have hP := torusPenalty_nonneg x
  have hR := mul_nonneg (sq_nonneg t) (sixthRegularizer_nonneg x)
  apply le_of_mul_le_mul_left (a := t) (a0 := ht)
  unfold perturbedEnergy at hmin
  rw [hy] at hmin
  nlinarith

#print axioms exists_box_minimizer
#print axioms box_minimizer_interior

end
end DInstabilityComplexity.Separation
