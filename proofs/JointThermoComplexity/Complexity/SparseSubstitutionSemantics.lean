module
public import proofs.JointThermoComplexity.Complexity.SparseSubstitution
public import proofs.JointThermoComplexity.Complexity.SparseIntegerSemantics

set_option autoImplicit false
@[expose] public section

/-! Exact evaluation of the ordered raw-list substitution. -/

namespace JointThermoComplexity.Complexity.SparseSubstitution
open SparseInteger
variable {V W : Type}

theorem eval_expand (f : V → Poly W) (x : W → ℝ) (vs : List V) :
    (interpret (expand f vs)).eval₂ (Int.castRingHom ℝ) x =
      (vs.map (fun v => (interpret (f v)).eval₂ (Int.castRingHom ℝ) x)).prod := by
  induction vs with
  | nil => simp [expand, interpret_constant]
  | cons v vs ih =>
    simp only [expand_cons, interpret_product, MvPolynomial.eval₂_mul, List.map_cons, List.prod_cons, ih]

theorem eval_substitute (f : V → Poly W) (x : W → ℝ) (p : Poly V) :
    (interpret (substitute f p)).eval₂ (Int.castRingHom ℝ) x =
      (interpret p).eval₂ (Int.castRingHom ℝ)
        (fun v => (interpret (f v)).eval₂ (Int.castRingHom ℝ) x) := by
  induction p with
  | nil => simp
  | cons a p ih =>
    simp only [substitute_cons, interpret_append, interpret_scale, interpret_cons,
      MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
      Int.coe_castRingHom, eval_expand, eval_monomial, ih]

theorem eval_cubeVariable (x : V → ℝ) (v : V) :
    (interpret (cubeVariable v)).eval₂ (Int.castRingHom ℝ) x = 2 * x v - 3 := by
  rw [eval_interpret]
  simp [cubeVariable, sub_eq_add_neg]

theorem eval_orthantVariable (x : V ⊕ V → ℝ) (v : V) :
    (interpret (orthantVariable v)).eval₂ (Int.castRingHom ℝ) x = x (.inl v) - x (.inr v) := by
  rw [eval_interpret]
  simp [orthantVariable, sub_eq_add_neg]

theorem eval_orthant (p : Poly V) (x : V ⊕ V → ℝ) :
    (interpret (orthant p)).eval₂ (Int.castRingHom ℝ) x =
      (interpret p).eval₂ (Int.castRingHom ℝ) (fun v => x (.inl v) - x (.inr v)) := by
  simpa only [orthant, eval_orthantVariable] using eval_substitute orthantVariable x p

end JointThermoComplexity.Complexity.SparseSubstitution

#print axioms JointThermoComplexity.Complexity.SparseSubstitution.eval_expand
#print axioms JointThermoComplexity.Complexity.SparseSubstitution.eval_substitute
#print axioms JointThermoComplexity.Complexity.SparseSubstitution.eval_orthant
