module
public import proofs.JointThermoComplexity.Complexity.SourceQuadraticActivation
public import proofs.JointThermoComplexity.Complexity.SourceTermCircuitSemantics

public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/- Adapted from DInstabilityComplexity/QuadraticActivationPolynomials.lean in the private
D-stability completeness development. Original source and SHA-256 are
preserved in SOURCE_QUADRATIC_CIRCUIT_ADAPTATION.json and syntax-inputs/.
The original package Apache-2.0 license is retained in
third_party/quadratic-witness/LICENSE.original. This version uses only
the independently defined RealSyntax; no source-hardness theorem is assumed. -/

/-! # Literal finite polynomial lists for equality and strict-sign activation -/

namespace JointThermoComplexity.Complexity.QuadraticCircuit

variable {n : ℕ} {V W : Type}

open MvPolynomial

noncomputable section

def equalityActivationEquations : List (MvPolynomial (Fin 3) ℤ) :=
  [X 0 * (X 0 - 1), X 0 * (X 1 - X 2)]

def strictSignEquations : List (MvPolynomial (Fin 6) ℤ) :=
  [X 0 * (X 0 - 1), X 4 - X 3 ^ 2, X 5 - (X 2 - X 1) * X 4, X 0 * (X 5 - 1)]

theorem equalityActivationEquations_iff (a l r : ℝ) :
    EquationsHold equalityActivationEquations ![a, l, r] ↔ EqualityActivation a l r := by
  simp [EquationsHold, equalityActivationEquations, EqualityActivation, BooleanBit, sub_eq_zero]

theorem strictSignEquations_iff (a l r y b c : ℝ) :
    EquationsHold strictSignEquations ![a, l, r, y, b, c] ↔ StrictSignActivation a l r y b c := by
  simp [EquationsHold, strictSignEquations, StrictSignActivation, BooleanBit, sub_eq_zero]

theorem strictSignEquations_exact (a l r : ℝ) :
    (∃ y b c : ℝ, EquationsHold strictSignEquations ![a, l, r, y, b, c]) ↔
      BooleanBit a ∧ (a = 0 ∨ l < r) := by
  simp only [strictSignEquations_iff, strictSignActivation_iff]

private theorem degree_variable {V : Type} (v : V) :
    (X v : MvPolynomial V ℤ).totalDegree ≤ 1 := le_of_eq (MvPolynomial.totalDegree_X v)

private theorem degree_var_sub_var {V : Type} (v w : V) :
    ((X v - X w) : MvPolynomial V ℤ).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le (degree_variable _) (degree_variable _))

private theorem degree_var_sub_one {V : Type} (v : V) :
    ((X v - 1) : MvPolynomial V ℤ).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le (degree_variable _) (by simp))

theorem equalityActivationEquations_quadratic (p : MvPolynomial (Fin 3) ℤ)
    (hp : p ∈ equalityActivationEquations) : p.totalDegree ≤ 2 := by
  simp only [equalityActivationEquations, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (degree_variable _) (degree_var_sub_one _))
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (degree_variable _) (degree_var_sub_var _ _))

theorem strictSignEquations_quadratic (p : MvPolynomial (Fin 6) ℤ)
    (hp : p ∈ strictSignEquations) : p.totalDegree ≤ 2 := by
  simp only [strictSignEquations, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (degree_variable _) (degree_var_sub_one _))
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le ((degree_variable _).trans (by decide : 1 ≤ 2))
    simpa only [MvPolynomial.totalDegree_X] using
      (MvPolynomial.totalDegree_pow (X 3 : MvPolynomial (Fin 6) ℤ) 2)
  · apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le ((degree_variable _).trans (by decide : 1 ≤ 2))
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (degree_var_sub_var _ _) (degree_variable _))
  · exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (degree_variable _) (degree_var_sub_one _))

#print axioms equalityActivationEquations_iff
#print axioms strictSignEquations_exact
#print axioms equalityActivationEquations_quadratic
#print axioms strictSignEquations_quadratic

end
end JointThermoComplexity.Complexity.QuadraticCircuit
