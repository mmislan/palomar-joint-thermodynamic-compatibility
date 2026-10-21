module
public import proofs.JointThermoComplexity.Complexity.SourceSparseTerm
public import proofs.JointThermoComplexity.Complexity.SourceClosedQuadratic

set_option autoImplicit false
@[expose] public section

/-! # Executable sparse quadratic circuits for complete source formulas

The equations below are literal integer lists. Their interpretation is the
previous activated circuit, including its shared original coordinates and
root activation. No witness is used in their construction.
-/

namespace JointThermoComplexity.Complexity.SparseCircuit
open RealSyntax QuadraticCircuit SparseInteger
variable {n : ℕ}

def equalityActivation : List (Poly (Fin 3)) :=
  [product (atom 0) (sub (atom 0) (constant 1)), product (atom 0) (sub (atom 1) (atom 2))]

def strictSign : List (Poly (Fin 6)) :=
  [product (atom 0) (sub (atom 0) (constant 1)), sub (atom 4) (square (atom 3)),
    sub (atom 5) (product (sub (atom 2) (atom 1)) (atom 4)), product (atom 0) (sub (atom 5) (constant 1))]

theorem equality_interpret : equalityActivation.map interpret = equalityActivationEquations := by
  simp only [equalityActivation, equalityActivationEquations, List.map_cons, List.map_nil,
    interpret_product, interpret_atom, interpret_sub, interpret_constant, map_one]

theorem strictSign_interpret : strictSign.map interpret = strictSignEquations := by
  simp only [strictSign, strictSignEquations, List.map_cons, List.map_nil,
    interpret_product, interpret_atom, interpret_sub, interpret_constant, interpret_square, map_one]

def formulaEquations : (p : Formula n) → List (Poly (Fin n ⊕ FormulaSlot p))
  | .truth => [product (atom (.inr ())) (sub (atom (.inr ())) (constant 1))]
  | .falsity => [atom (.inr ())]
  | .eq s t =>
    ((termEquations s).map (relabel (atomLeft s t)) ++
      (termEquations t).map (relabel (atomRight s t))) ++
      equalityActivation.map (relabel (atomEqualityPorts s t))
  | .lt s t =>
    ((termEquations s).map (relabel (atomLeft s t)) ++
      (termEquations t).map (relabel (atomRight s t))) ++
      strictSign.map (relabel (atomPorts s t))
  | .conj p q =>
    ((formulaEquations p).map (relabel (formulaLeft p q)) ++
      (formulaEquations q).map (relabel (formulaRight p q))) ++
      [product (atom (.inr (.inl ()))) (sub (atom (.inr (.inl ()))) (constant 1)),
        sub (atom (.inr (.inr (.inl (formulaRoot p))))) (atom (.inr (.inl ()))),
        sub (atom (.inr (.inr (.inr (formulaRoot q))))) (atom (.inr (.inl ())))]
  | .disj p q =>
    ((formulaEquations p).map (relabel (formulaLeft p q)) ++
      (formulaEquations q).map (relabel (formulaRight p q))) ++
      [product (atom (.inr (.inl ()))) (sub (atom (.inr (.inl ()))) (constant 1)),
        sub (add (atom (.inr (.inr (.inl (formulaRoot p)))))
          (atom (.inr (.inr (.inr (formulaRoot q)))))) (atom (.inr (.inl ())))]

theorem formula_interpret (p : Formula n) :
    (formulaEquations p).map interpret = QuadraticCircuit.formulaEquations p := by
  induction p with
  | truth => simp only [formulaEquations, QuadraticCircuit.formulaEquations, List.map_cons, List.map_nil,
      interpret_product, interpret_atom, interpret_sub, interpret_constant, map_one]
  | falsity => simp only [formulaEquations, QuadraticCircuit.formulaEquations, List.map_cons, List.map_nil, interpret_atom]
  | eq s t => simp only [formulaEquations, QuadraticCircuit.formulaEquations, List.map_append,
      interpret_relabel_list, term_interpret, equality_interpret]
  | lt s t => simp only [formulaEquations, QuadraticCircuit.formulaEquations, List.map_append,
      interpret_relabel_list, term_interpret, strictSign_interpret]
  | conj p q hp hq => simp only [formulaEquations, QuadraticCircuit.formulaEquations, List.map_append,
      interpret_relabel_list, hp, hq, List.map_cons, List.map_nil,
      interpret_product, interpret_atom, interpret_sub, interpret_constant, map_one]
  | disj p q hp hq => simp only [formulaEquations, QuadraticCircuit.formulaEquations, List.map_append,
      interpret_relabel_list, hp, hq, List.map_cons, List.map_nil,
      interpret_product, interpret_atom, interpret_sub, interpret_add, interpret_constant, map_one]

def closedEquations (p : Formula n) : List (Poly (Fin n ⊕ FormulaSlot p)) :=
  formulaEquations p ++ [sub (atom (.inr (formulaRoot p))) (constant 1)]

theorem closed_interpret (p : Formula n) :
    (closedEquations p).map interpret = closedFormulaEquations p := by
  simp only [closedEquations, closedFormulaEquations, List.map_append, formula_interpret,
    List.map_cons, List.map_nil, interpret_sub, interpret_atom, interpret_constant, map_one]

theorem closed_satisfiable_iff (p : Formula n) :
    (∃ x : Fin n ⊕ FormulaSlot p → ℝ,
      ∀ q ∈ closedEquations p, (interpret q).eval₂ (Int.castRingHom ℝ) x = 0) ↔ ∃ ρ, p.eval ρ := by
  rw [← closedFormulaEquations_satisfiable_iff p, ← closed_interpret p]
  simp only [EquationsHold, List.forall_mem_map]

theorem closed_equation_count (p : Formula n) : (closedEquations p).length ≤ 4 * p.size + 1 := by
  have h := closedFormulaEquations_length_le p
  rw [← closed_interpret p, List.length_map] at h
  exact h

theorem closed_equations_degree (p : Formula n) (q : Poly (Fin n ⊕ FormulaSlot p)) (hq : q ∈ closedEquations p) :
    (interpret q).totalDegree ≤ 2 :=
  closedFormulaEquations_quadratic p _ (by rw [← closed_interpret p]; exact List.mem_map.mpr ⟨q, hq, rfl⟩)

end JointThermoComplexity.Complexity.SparseCircuit

#print axioms JointThermoComplexity.Complexity.SparseCircuit.formula_interpret
#print axioms JointThermoComplexity.Complexity.SparseCircuit.closed_satisfiable_iff
#print axioms JointThermoComplexity.Complexity.SparseCircuit.closed_equation_count
#print axioms JointThermoComplexity.Complexity.SparseCircuit.closed_equations_degree
