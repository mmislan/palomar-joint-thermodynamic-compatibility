module
public import proofs.JointThermoComplexity.Complexity.ExactScaleChain

set_option autoImplicit false
@[expose] public section

/-! # One positive scale chain shared by an entire integer quadratic system

The terminal chain coordinate is wired into every homogenized equation.
All roots force the same positive terminal scale. The exact real assignment
is a mathematical witness, distinct from the literal integer family.
-/

namespace JointThermoComplexity.Complexity.ScaledQuadraticSystem
open MvPolynomial QuadraticHomogenization SourceIntegerWeight FixedQuarterSquaring
variable {V A : Type}

def liftPorts (m : ℕ) : V ⊕ Unit → V ⊕ Fin (m + 1) :=
  Sum.elim Sum.inl (fun _ => .inr (Fin.last m))

noncomputable def family (q : A → MvPolynomial V ℤ) (m : ℕ) :
    A ⊕ (Unit ⊕ Fin m) → MvPolynomial (V ⊕ Fin (m + 1)) ℤ :=
  Sum.elim (fun j => rename (liftPorts m) (quadraticLift (q j)))
    (fun j => rename Sum.inr (ExactScaleChain.equation m j))

theorem liftPorts_assignment (m : ℕ) (u : V → ℝ) (y : Fin (m + 1) → ℝ) :
    (Sum.elim u y) ∘ liftPorts m = Sum.elim u (fun _ => y (Fin.last m)) := by
  funext i
  cases i <;> rfl

theorem eval_source (q : A → MvPolynomial V ℤ) (m : ℕ) (u : V → ℝ)
    (y : Fin (m + 1) → ℝ) (j : A) :
    (family q m (.inl j)).eval₂ (Int.castRingHom ℝ) (Sum.elim u y) =
      (quadraticLift (q j)).eval₂ (Int.castRingHom ℝ) (Sum.elim u (fun _ => y (Fin.last m))) := by
  simp only [family, Sum.elim_inl, MvPolynomial.eval₂_rename, liftPorts_assignment]

theorem eval_scale (q : A → MvPolynomial V ℤ) (m : ℕ) (u : V → ℝ)
    (y : Fin (m + 1) → ℝ) (j : Unit ⊕ Fin m) :
    (family q m (.inr j)).eval₂ (Int.castRingHom ℝ) (Sum.elim u y) =
      (ExactScaleChain.equation m j).eval₂ (Int.castRingHom ℝ) y := by
  simp only [family, Sum.elim_inr, MvPolynomial.eval₂_rename, Function.comp_def, Sum.elim_inr]

theorem roots_iff (q : A → MvPolynomial V ℤ) (hq : ∀ j, (q j).totalDegree ≤ 2)
    (m : ℕ) (u : V → ℝ) (y : Fin (m + 1) → ℝ) :
    (∀ j, (family q m j).eval₂ (Int.castRingHom ℝ) (Sum.elim u y) = 0) ↔
      (∀ i, y i = exactChain i.val) ∧
        ∀ j, (q j).eval₂ (Int.castRingHom ℝ) (fun i => u i / exactChain m) = 0 := by
  constructor
  · intro h
    have hy : ∀ j, (ExactScaleChain.equation m j).eval₂ (Int.castRingHom ℝ) y = 0 := by
      intro j
      simpa only [eval_scale] using h (.inr j)
    have hexact := (ExactScaleChain.roots_iff_exact m y).mp hy
    have hterminal : y (Fin.last m) = exactChain m := hexact (Fin.last m)
    refine ⟨hexact, ?_⟩
    intro j
    have hj : (quadraticLift (q j)).eval₂ (Int.castRingHom ℝ)
        (Sum.elim u (fun _ => y (Fin.last m))) = 0 := by
      simpa only [eval_source] using h (.inl j)
    rw [hterminal] at hj
    exact (quadraticLift_zero_iff (q j) (hq j) u (exactChain m) (ne_of_gt (exactChain_pos m))).mp hj
  · rintro ⟨hy, hqroot⟩ j
    have hterminal : y (Fin.last m) = exactChain m := hy (Fin.last m)
    cases j with
    | inl j =>
      rw [eval_source, hterminal]
      exact (quadraticLift_zero_iff (q j) (hq j) u (exactChain m)
        (ne_of_gt (exactChain_pos m))).mpr (hqroot j)
    | inr j =>
      rw [eval_scale]
      exact (ExactScaleChain.roots_iff_exact m y).mpr hy j

noncomputable def exactAssignment (m : ℕ) (x : V → ℝ) : V ⊕ Fin (m + 1) → ℝ :=
  Sum.elim (fun i => exactChain m * x i) (fun i => exactChain i.val)

theorem exactAssignment_root (q : A → MvPolynomial V ℤ) (hq : ∀ j, (q j).totalDegree ≤ 2)
    (m : ℕ) (x : V → ℝ) (hx : ∀ j, (q j).eval₂ (Int.castRingHom ℝ) x = 0) :
    ∀ j, (family q m j).eval₂ (Int.castRingHom ℝ) (exactAssignment m x) = 0 := by
  intro j
  cases j with
  | inl j =>
    rw [exactAssignment, eval_source]
    change (quadraticLift (q j)).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (fun i => exactChain m * x i) (fun _ => exactChain m)) = 0
    exact common_scaled_root q hq x hx (exactChain m) j
  | inr j =>
    rw [exactAssignment, eval_scale]
    exact ExactScaleChain.exact_values_are_roots m j

theorem root_recovery (q : A → MvPolynomial V ℤ) (hq : ∀ j, (q j).totalDegree ≤ 2)
    (m : ℕ) (v : V ⊕ Fin (m + 1) → ℝ)
    (hv : ∀ j, (family q m j).eval₂ (Int.castRingHom ℝ) v = 0) :
    ∀ j, (q j).eval₂ (Int.castRingHom ℝ) (fun i => v (.inl i) / exactChain m) = 0 := by
  have he : Sum.elim (fun i => v (.inl i)) (fun i => v (.inr i)) = v := by
    funext i
    cases i <;> rfl
  exact ((roots_iff q hq m _ _).mp (by rw [he]; exact hv)).2

theorem common_root_iff (q : A → MvPolynomial V ℤ) (hq : ∀ j, (q j).totalDegree ≤ 2) (m : ℕ) :
    (∃ v, ∀ j, (family q m j).eval₂ (Int.castRingHom ℝ) v = 0) ↔
      ∃ x, ∀ j, (q j).eval₂ (Int.castRingHom ℝ) x = 0 := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨_, root_recovery q hq m v hv⟩
  · rintro ⟨x, hx⟩
    exact ⟨exactAssignment m x, exactAssignment_root q hq m x hx⟩

theorem exactAssignment_quarter (m : ℕ) (x : V → ℝ)
    (hx : ∀ i, |exactChain m * x i| ≤ 1 / 4) :
    ∀ i, |exactAssignment m x i| ≤ 1 / 4 := by
  intro i
  cases i with
  | inl i => exact hx i
  | inr i =>
    change |exactChain i.val| ≤ 1 / 4
    rw [abs_of_pos (exactChain_pos i.val)]
    exact exactChain_le_quarter i.val

theorem family_degree (q : A → MvPolynomial V ℤ) (m : ℕ) (j : A ⊕ (Unit ⊕ Fin m)) :
    (family q m j).totalDegree ≤ 2 := by
  cases j with
  | inl j => exact (MvPolynomial.totalDegree_rename_le _ _).trans (quadraticLift_degree (q j))
  | inr j => exact (MvPolynomial.totalDegree_rename_le _ _).trans (ExactScaleChain.equation_degree m j)

theorem family_weight (q : A → MvPolynomial V ℤ) (W : ℕ) (hW : ∀ j, weight (q j) ≤ W)
    (m : ℕ) (j : A ⊕ (Unit ⊕ Fin m)) : weight (family q m j) ≤ 3 * W + 5 := by
  cases j with
  | inl j =>
    have h := (weight_rename (liftPorts m) (quadraticLift (q j))).trans (quadraticLift_weight_le (q j))
    have hq := hW j
    change weight (rename (liftPorts m) (quadraticLift (q j))) ≤ 3 * W + 5
    omega
  | inr j =>
    exact ((weight_rename Sum.inr (ExactScaleChain.equation m j)).trans
      (ExactScaleChain.equation_weight m j)).trans (by omega)

theorem coordinate_count [Fintype V] (m : ℕ) :
    Fintype.card (V ⊕ Fin (m + 1)) = Fintype.card V + m + 1 := by
  rw [Fintype.card_sum, Fintype.card_fin]
  omega

theorem equation_count [Fintype A] (m : ℕ) :
    Fintype.card (A ⊕ (Unit ⊕ Fin m)) = Fintype.card A + m + 1 := by
  rw [Fintype.card_sum, ExactScaleChain.equation_count]
  omega

end JointThermoComplexity.Complexity.ScaledQuadraticSystem

#print axioms JointThermoComplexity.Complexity.ScaledQuadraticSystem.roots_iff
#print axioms JointThermoComplexity.Complexity.ScaledQuadraticSystem.common_root_iff
#print axioms JointThermoComplexity.Complexity.ScaledQuadraticSystem.family_degree
#print axioms JointThermoComplexity.Complexity.ScaledQuadraticSystem.family_weight
