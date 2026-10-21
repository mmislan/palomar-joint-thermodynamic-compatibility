module
public import proofs.JointThermoComplexity.Complexity.SourceMinimumSeparation

set_option autoImplicit false
@[expose] public section

/-! # Concrete quadratic circle padding supplies the coercivity bound

Each original coordinate is paired with a second coordinate on a circle of
radius one quarter. All padded common zeros lie strictly inside the half cube.
The sum of squared circle equations controls every coordinate on the entire
real space, so the global minimum separation theorem applies without an
externally supplied coercivity certificate. Scaling the source into this
quarter cube and implementing its binary reduction remain separate work.
-/

namespace JointThermoComplexity.Complexity.SourceSeparation
open MvPolynomial DInstabilityComplexity.Separation
variable {ι α : Type}

noncomputable def quarterCirclePolynomial (i : ι) : MvPolynomial (ι × Bool) ℤ :=
  C 16 * (X (i, false) ^ 2 + X (i, true) ^ 2) - 1

noncomputable def circlePadding (q : α → MvPolynomial ι ℤ) :
    α ⊕ ι → MvPolynomial (ι × Bool) ℤ :=
  Sum.elim (fun j => rename (fun i => (i, false)) (q j)) quarterCirclePolynomial

theorem eval_quarterCirclePolynomial (i : ι) (x : ι × Bool → ℝ) :
    (quarterCirclePolynomial i).eval₂ (Int.castRingHom ℝ) x =
      16 * (x (i, false) ^ 2 + x (i, true) ^ 2) - 1 := by
  simp [quarterCirclePolynomial]

theorem quarterCirclePolynomial_quadratic (i : ι) :
    (quarterCirclePolynomial i).totalDegree ≤ 2 := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le _ (by simp)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · simpa only [MvPolynomial.totalDegree_X] using
      (MvPolynomial.totalDegree_pow (X (i, false) : MvPolynomial (ι × Bool) ℤ) 2)
  · simpa only [MvPolynomial.totalDegree_X] using
      (MvPolynomial.totalDegree_pow (X (i, true) : MvPolynomial (ι × Bool) ℤ) 2)

theorem circlePadding_quadratic (q : α → MvPolynomial ι ℤ)
    (hq : ∀ j, (q j).totalDegree ≤ 2) (j : α ⊕ ι) :
    (circlePadding q j).totalDegree ≤ 2 := by
  cases j with
  | inl j => exact (MvPolynomial.totalDegree_rename_le _ _).trans (hq j)
  | inr i => exact quarterCirclePolynomial_quadratic i

private theorem quarterCircle_abs_le {a b : ℝ} (h : 16 * (a ^ 2 + b ^ 2) - 1 = 0) :
    |a| ≤ 1 / 4 := by
  have ha := abs_nonneg a
  have hs := sq_abs a
  have hb := sq_nonneg b
  nlinarith

theorem circlePadding_zero_bounds (q : α → MvPolynomial ι ℤ) (x : ι × Bool → ℝ)
    (hx : ∀ j, (circlePadding q j).eval₂ (Int.castRingHom ℝ) x = 0) :
    ∀ i, |x i| ≤ 1 / 4 := by
  rintro ⟨i, b⟩
  have h := hx (.inr i)
  change (quarterCirclePolynomial i).eval₂ (Int.castRingHom ℝ) x = 0 at h
  rw [eval_quarterCirclePolynomial] at h
  cases b with
  | false => exact quarterCircle_abs_le h
  | true => exact quarterCircle_abs_le (by nlinarith [h] : 16 * (x (i, true) ^ 2 + x (i, false) ^ 2) - 1 = 0)

theorem circlePadding_root_iff (q : α → MvPolynomial ι ℤ) :
    (∃ x, ∀ j, (circlePadding q j).eval₂ (Int.castRingHom ℝ) x = 0) ↔
      ∃ u : ι → ℝ, (∀ i, |u i| ≤ 1 / 4) ∧ ∀ j, (q j).eval₂ (Int.castRingHom ℝ) u = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun i => x (i, false), fun i => circlePadding_zero_bounds q x hx (i, false), ?_⟩
    intro j
    simpa only [circlePadding, Sum.elim_inl, MvPolynomial.eval₂_rename, Function.comp_def] using hx (.inl j)
  · rintro ⟨u, hu, hq⟩
    let x : ι × Bool → ℝ := fun i => if i.2 then Real.sqrt (1 / 16 - u i.1 ^ 2) else u i.1
    refine ⟨x, ?_⟩
    intro j
    cases j with
    | inl j =>
      change (rename (fun i => (i, false)) (q j)).eval₂ (Int.castRingHom ℝ) x = 0
      rw [MvPolynomial.eval₂_rename]
      change (q j).eval₂ (Int.castRingHom ℝ) u = 0
      exact hq j
    | inr i =>
      have hnonneg : 0 ≤ 1 / 16 - u i ^ 2 := by
        have ha := hu i
        have hp := abs_nonneg (u i)
        have hs := sq_abs (u i)
        nlinarith
      change (quarterCirclePolynomial i).eval₂ (Int.castRingHom ℝ) x = 0
      rw [eval_quarterCirclePolynomial]
      change 16 * (u i ^ 2 + (Real.sqrt (1 / 16 - u i ^ 2)) ^ 2) - 1 = 0
      rw [Real.sq_sqrt hnonneg]
      ring

private theorem abs_le_circle_defect_sq_add_two (a b : ℝ) :
    |a| ≤ (16 * (a ^ 2 + b ^ 2) - 1) ^ 2 + 2 := by
  by_cases ha : |a| ≤ 2
  · linarith only [ha, sq_nonneg (16 * (a ^ 2 + b ^ 2) - 1)]
  · have hapos : 2 < |a| := lt_of_not_ge ha
    have hd : |a| ≤ 16 * (a ^ 2 + b ^ 2) - 1 := by
      nlinarith [sq_abs a, sq_nonneg b]
    have hdpos : 1 ≤ 16 * (a ^ 2 + b ^ 2) - 1 := by linarith only [hapos, hd]
    have hdsq : 16 * (a ^ 2 + b ^ 2) - 1 ≤ (16 * (a ^ 2 + b ^ 2) - 1) ^ 2 := by
      nlinarith only [hdpos]
    linarith only [hd, hdsq]

variable [Fintype ι] [Fintype α] [DecidableEq ι]

omit [DecidableEq ι] in
theorem circlePadding_coercive (q : α → MvPolynomial ι ℤ) (x : ι × Bool → ℝ)
    (i : ι × Bool) : |x i| ≤ quadraticEnergy (circlePadding q) x + 2 := by
  classical
  rcases i with ⟨i, b⟩
  have hterm : (16 * (x (i, false) ^ 2 + x (i, true) ^ 2) - 1) ^ 2 ≤
      quadraticEnergy (circlePadding q) x := by
    rw [quadraticEnergy_eq_sum]
    have hs := Finset.single_le_sum (f := fun j : α ⊕ ι =>
      ((circlePadding q j).eval₂ (Int.castRingHom ℝ) x) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ (Sum.inr i))
    simpa only [circlePadding, Sum.elim_inr, eval_quarterCirclePolynomial] using hs
  have hb : |x (i, b)| ≤ (16 * (x (i, false) ^ 2 + x (i, true) ^ 2) - 1) ^ 2 + 2 := by
    cases b with
    | false => exact abs_le_circle_defect_sq_add_two _ _
    | true =>
      simpa only [add_comm (x (i, true) ^ 2) (x (i, false) ^ 2)] using
        abs_le_circle_defect_sq_add_two (x (i, true)) (x (i, false))
  linarith only [hb, hterm]

theorem circlePadding_energy_gap (q : α → MvPolynomial ι ℤ)
    (hq : ∀ j, (q j).totalDegree ≤ 2)
    (hno : ¬ ∃ u : ι → ℝ, (∀ i, |u i| ≤ 1 / 4) ∧
      ∀ j, (q j).eval₂ (Int.castRingHom ℝ) u = 0) :
    ∀ x, 1 / ((minimumHeight (circlePadding q) : ℝ) + 1) < quadraticEnergy (circlePadding q) x :=
  coercive_quadratic_energy_gap (circlePadding q) (circlePadding_quadratic q hq) 2
    (circlePadding_coercive q) (fun h => hno ((circlePadding_root_iff q).mp h))

end JointThermoComplexity.Complexity.SourceSeparation

#print axioms JointThermoComplexity.Complexity.SourceSeparation.circlePadding_root_iff
#print axioms JointThermoComplexity.Complexity.SourceSeparation.circlePadding_coercive
#print axioms JointThermoComplexity.Complexity.SourceSeparation.circlePadding_energy_gap
