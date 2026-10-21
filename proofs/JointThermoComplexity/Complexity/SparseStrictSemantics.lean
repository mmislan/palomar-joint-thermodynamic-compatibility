module
public import proofs.JointThermoComplexity.Complexity.SparseStrictPolynomial
public import proofs.JointThermoComplexity.Complexity.SparseCircleSemantics
public import proofs.JointThermoComplexity.Complexity.StrictPolynomialCore
public import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
@[expose] public section

/-! # Exact algebraic agreement for executable circle/strict polynomial data

Finite sum enumeration, integer error clearing, circle reindexing and both
strict builders agree with the mathematical polynomials used by the source
normal forms. This bridge makes no binary running-time claim.
-/

namespace JointThermoComplexity.Complexity.SparseStrictPolynomial
open SparseInteger DInstabilityComplexity.Separation
variable {V A : Type} {n : ℕ}

theorem interpret_flatten (ps : List (SparseInteger.Poly V)) : interpret ps.flatten = (ps.map interpret).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp only [List.flatten_cons, interpret_append, List.map_cons, List.sum_cons, ih]

theorem interpret_sumFamily (q : Fin n → SparseInteger.Poly V) : interpret (sumFamily q) = ∑ j, interpret (q j) := by
  rw [sumFamily, interpret_flatten, List.map_ofFn, List.sum_ofFn]
  rfl

theorem interpret_energy (q : Fin n → SparseInteger.Poly V) :
    interpret (energy q) = quadraticEnergyPolynomial (fun j => interpret (q j)) := by
  simp only [energy, interpret_sumFamily, interpret_square, quadraticEnergyPolynomial]

theorem interpret_edge (k : ℕ) (i : Fin (k + 1)) : interpret (edge k i) = IntegerChainError.edge k i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [edge, Fin.cases_zero, IntegerChainError.edge_zero, interpret_sub,
      interpret_scale, interpret_atom, interpret_constant, map_one]
  · simp only [edge, Fin.cases_succ, IntegerChainError.edge_succ, interpret_scale,
      interpret_sub, interpret_atom, interpret_square]

theorem interpret_error (k : ℕ) : interpret (error k) = IntegerChainError.errorPolynomial k := by
  simp only [error, interpret_energy, quadraticEnergyPolynomial, interpret_edge, IntegerChainError.errorPolynomial]

theorem interpret_bounded (q : Fin n → SparseInteger.Poly V) (k : ℕ) :
    interpret (bounded q k) = StrictPolynomialCore.bounded (fun j => interpret (q j)) k := by
  simp only [bounded, interpret_sub, interpret_scale, interpret_square, interpret_atom,
    interpret_relabel, interpret_energy, interpret_error, StrictPolynomialCore.bounded]

theorem interpret_allReal (q : Fin n → SparseInteger.Poly V) (k : ℕ) :
    interpret (allReal q k) = StrictPolynomialCore.allReal (fun j => interpret (q j)) k := by
  simp only [allReal, interpret_sub, interpret_scale, interpret_product, interpret_square, interpret_atom,
    interpret_constant, map_one, interpret_relabel, interpret_energy, interpret_error, StrictPolynomialCore.allReal]
  ring

theorem interpreted_bounded_degree (q : Fin n → SparseInteger.Poly V) (hq : ∀ j, DegreeLE 2 (q j)) (k : ℕ) :
    (interpret (bounded q k)).totalDegree ≤ 4 := SparseInteger.interpret_degree _ (bounded_degree q hq k)

theorem interpreted_allReal_degree (q : Fin n → SparseInteger.Poly V) (hq : ∀ j, DegreeLE 2 (q j)) (k : ℕ) :
    (interpret (allReal q k)).totalDegree ≤ 4 := SparseInteger.interpret_degree _ (allReal_degree q hq k)

theorem bounded_circle_agreement (q : A → SparseInteger.Poly V) (e : A ⊕ V ≃ Fin n) (k : ℕ) :
    interpret (bounded (fun j => SparseCirclePadding.family q (e.symm j)) k) =
      StrictPolynomialCore.bounded (fun j => SourceSeparation.circlePadding (fun a => interpret (q a)) (e.symm j)) k := by
  simp only [interpret_bounded, SparseCirclePadding.interpret_family]

theorem allReal_circle_agreement (q : A → SparseInteger.Poly V) (e : A ⊕ V ≃ Fin n) (k : ℕ) :
    interpret (allReal (fun j => SparseCirclePadding.family q (e.symm j)) k) =
      StrictPolynomialCore.allReal (fun j => SourceSeparation.circlePadding (fun a => interpret (q a)) (e.symm j)) k := by
  simp only [interpret_allReal, SparseCirclePadding.interpret_family]

end JointThermoComplexity.Complexity.SparseStrictPolynomial

#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.interpret_bounded
#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.interpret_allReal
#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.interpreted_bounded_degree
#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.bounded_circle_agreement
#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.allReal_circle_agreement
