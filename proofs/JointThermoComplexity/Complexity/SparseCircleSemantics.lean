module
public import proofs.JointThermoComplexity.Complexity.SparseCirclePadding
public import proofs.JointThermoComplexity.Complexity.SparseIntegerSemantics
public import proofs.JointThermoComplexity.Complexity.SourceCirclePadding

set_option autoImplicit false
@[expose] public section

/-! # Exact semantic bridge for executable sparse circle padding -/

namespace JointThermoComplexity.Complexity.SparseCirclePadding
open SparseInteger SourceSeparation DInstabilityComplexity.Separation
variable {V A : Type}

theorem interpret_circle (i : V) : interpret (circle i) = quarterCirclePolynomial i := by
  simp only [circle, quarterCirclePolynomial, interpret_sub, interpret_scale, interpret_add,
    interpret_square, interpret_atom, interpret_constant, map_one]

theorem interpret_family (q : A → SparseInteger.Poly V) (j : A ⊕ V) :
    interpret (family q j) = circlePadding (fun j => interpret (q j)) j := by
  cases j with
  | inl j => simp only [family, circlePadding, Sum.elim_inl, interpret_relabel]
  | inr i => simp only [family, circlePadding, Sum.elim_inr, interpret_circle]

theorem root_iff (q : A → SparseInteger.Poly V) :
    (∃ x : V × Bool → ℝ, ∀ j, (interpret (family q j)).eval₂ (Int.castRingHom ℝ) x = 0) ↔
      ∃ u : V → ℝ, (∀ i, |u i| ≤ 1 / 4) ∧ ∀ j, (interpret (q j)).eval₂ (Int.castRingHom ℝ) u = 0 := by
  simp only [interpret_family]
  exact circlePadding_root_iff (fun j => interpret (q j))

theorem root_quarter (q : A → SparseInteger.Poly V) (x : V × Bool → ℝ)
    (hx : ∀ j, (interpret (family q j)).eval₂ (Int.castRingHom ℝ) x = 0) :
    ∀ i, |x i| ≤ 1 / 4 :=
  circlePadding_zero_bounds (fun j => interpret (q j)) x (by simpa only [interpret_family] using hx)

theorem coercive [Fintype V] [Fintype A]
    (q : A → SparseInteger.Poly V) (x : V × Bool → ℝ) (i : V × Bool) :
    |x i| ≤ quadraticEnergy (fun j => interpret (family q j)) x + 2 := by
  simpa only [interpret_family] using circlePadding_coercive (fun j => interpret (q j)) x i

end JointThermoComplexity.Complexity.SparseCirclePadding

#print axioms JointThermoComplexity.Complexity.SparseCirclePadding.interpret_family
#print axioms JointThermoComplexity.Complexity.SparseCirclePadding.root_iff
#print axioms JointThermoComplexity.Complexity.SparseCirclePadding.root_quarter
#print axioms JointThermoComplexity.Complexity.SparseCirclePadding.coercive
