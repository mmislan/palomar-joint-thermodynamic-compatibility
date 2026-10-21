module
public import proofs.JointThermoComplexity.Complexity.HomogeneousEvaluation
public import Mathlib.Algebra.MvPolynomial.CommRing

set_option autoImplicit false
@[expose] public section

/-! # Integer quadratic homogenization with one common scale coordinate

The polynomial uses only the degree0, degree1 and degree2 components. Its
degree is always at most two; exact recovery requires the original polynomial
to have degree at most two and the shared scale to be nonzero.
-/

namespace JointThermoComplexity.Complexity.QuadraticHomogenization
open MvPolynomial HomogeneousEvaluation
variable {V : Type}

noncomputable def quadraticLift (p : MvPolynomial V ℤ) : MvPolynomial (V ⊕ Unit) ℤ :=
  rename Sum.inl (homogeneousComponent 0 p) * X (.inr ()) ^ 2 +
    rename Sum.inl (homogeneousComponent 1 p) * X (.inr ()) +
      rename Sum.inl (homogeneousComponent 2 p)

theorem renamed_component_degree (p : MvPolynomial V ℤ) (k : ℕ) :
    (rename (Sum.inl : V → V ⊕ Unit) (homogeneousComponent k p)).totalDegree ≤ k :=
  (MvPolynomial.totalDegree_rename_le _ _).trans
    (homogeneousComponent_isHomogeneous k p).totalDegree_le

theorem quadraticLift_degree (p : MvPolynomial V ℤ) : (quadraticLift p).totalDegree ≤ 2 := by
  have hs : (X (.inr ()) : MvPolynomial (V ⊕ Unit) ℤ).totalDegree ≤ 1 :=
    le_of_eq (MvPolynomial.totalDegree_X _)
  have hs2 : ((X (.inr ()) : MvPolynomial (V ⊕ Unit) ℤ) ^ 2).totalDegree ≤ 2 := by
    simpa only [MvPolynomial.totalDegree_X] using
      MvPolynomial.totalDegree_pow (X (.inr ()) : MvPolynomial (V ⊕ Unit) ℤ) 2
  unfold quadraticLift
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le _ (renamed_component_degree p 2)
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (renamed_component_degree p 0) hs2)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (renamed_component_degree p 1) hs)

theorem eval_quadraticLift (p : MvPolynomial V ℤ) (u : V → ℝ) (s : ℝ) :
    (quadraticLift p).eval₂ (Int.castRingHom ℝ) (Sum.elim u (fun _ => s)) =
      (homogeneousComponent 0 p).eval₂ (Int.castRingHom ℝ) u * s ^ 2 +
        (homogeneousComponent 1 p).eval₂ (Int.castRingHom ℝ) u * s +
          (homogeneousComponent 2 p).eval₂ (Int.castRingHom ℝ) u := by
  simp only [quadraticLift, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, MvPolynomial.eval₂_rename,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr]

theorem eval_quadraticLift_scaled (p : MvPolynomial V ℤ) (hp : p.totalDegree ≤ 2)
    (x : V → ℝ) (s : ℝ) :
    (quadraticLift p).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (fun i => s * x i) (fun _ => s)) = s ^ 2 * p.eval₂ (Int.castRingHom ℝ) x := by
  have hdecomp := congrArg (fun q : MvPolynomial V ℤ => q.eval₂ (Int.castRingHom ℝ) x)
    (quadratic_components p hp)
  simp only [MvPolynomial.eval₂_add] at hdecomp
  rw [eval_quadraticLift, component_eval_scale p 0 s x, component_eval_scale p 1 s x,
    component_eval_scale p 2 s x]
  rw [← hdecomp]
  ring

theorem eval_quadraticLift_div (p : MvPolynomial V ℤ) (hp : p.totalDegree ≤ 2)
    (u : V → ℝ) (s : ℝ) (hs : s ≠ 0) :
    (quadraticLift p).eval₂ (Int.castRingHom ℝ) (Sum.elim u (fun _ => s)) =
      s ^ 2 * p.eval₂ (Int.castRingHom ℝ) (fun i => u i / s) := by
  have h := eval_quadraticLift_scaled p hp (fun i => u i / s) s
  have hrecover : (fun i => s * (u i / s)) = u := by
    funext i
    rw [mul_comm s (u i / s)]
    exact div_mul_cancel₀ _ hs
  rw [hrecover] at h
  exact h

theorem quadraticLift_zero_iff (p : MvPolynomial V ℤ) (hp : p.totalDegree ≤ 2)
    (u : V → ℝ) (s : ℝ) (hs : s ≠ 0) :
    (quadraticLift p).eval₂ (Int.castRingHom ℝ) (Sum.elim u (fun _ => s)) = 0 ↔
      p.eval₂ (Int.castRingHom ℝ) (fun i => u i / s) = 0 := by
  rw [eval_quadraticLift_div p hp u s hs, mul_eq_zero]
  simp only [pow_ne_zero 2 hs, false_or]

variable {A : Type}

theorem common_scaled_root (q : A → MvPolynomial V ℤ) (hq : ∀ j, (q j).totalDegree ≤ 2)
    (x : V → ℝ) (hx : ∀ j, (q j).eval₂ (Int.castRingHom ℝ) x = 0) (s : ℝ) :
    ∀ j, (quadraticLift (q j)).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (fun i => s * x i) (fun _ => s)) = 0 := by
  intro j
  rw [eval_quadraticLift_scaled (q j) (hq j), hx j, mul_zero]

theorem common_root_recovery (q : A → MvPolynomial V ℤ) (hq : ∀ j, (q j).totalDegree ≤ 2)
    (u : V → ℝ) (s : ℝ) (hs : s ≠ 0)
    (hu : ∀ j, (quadraticLift (q j)).eval₂ (Int.castRingHom ℝ) (Sum.elim u (fun _ => s)) = 0) :
    ∀ j, (q j).eval₂ (Int.castRingHom ℝ) (fun i => u i / s) = 0 :=
  fun j => (quadraticLift_zero_iff (q j) (hq j) u s hs).mp (hu j)

end JointThermoComplexity.Complexity.QuadraticHomogenization

#print axioms JointThermoComplexity.Complexity.QuadraticHomogenization.quadraticLift_degree
#print axioms JointThermoComplexity.Complexity.QuadraticHomogenization.eval_quadraticLift_scaled
#print axioms JointThermoComplexity.Complexity.QuadraticHomogenization.quadraticLift_zero_iff
#print axioms JointThermoComplexity.Complexity.QuadraticHomogenization.common_root_recovery
