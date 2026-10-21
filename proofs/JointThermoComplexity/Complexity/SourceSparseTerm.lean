module
public import proofs.JointThermoComplexity.Complexity.SparseIntegerSemantics
public import proofs.JointThermoComplexity.Complexity.SourceTermCircuitData

set_option autoImplicit false
@[expose] public section

/-! # Executable sparse quadratic circuits for source terms

The source terms are traversed structurally; no real value or polynomial
support is inspected. Exact agreement with the previously checked quadratic
operation equations is proved below.
-/

namespace JointThermoComplexity.Complexity.SparseCircuit
open RealSyntax QuadraticCircuit SparseInteger
variable {n : ℕ} {V W : Type}

theorem interpret_relabel_list (f : V → W) (ps : List (Poly V)) :
    (ps.map (relabel f)).map interpret = (ps.map interpret).map (MvPolynomial.rename f) := by
  simp only [List.map_map, Function.comp_def, interpret_relabel]

def termEquations : (t : Term n) → List (Poly (Fin n ⊕ TermSlot t))
  | .int z => [sub (atom (.inr ())) (constant z)]
  | .var v => [sub (atom (.inr ())) (atom (.inl v))]
  | .add s t =>
    ((termEquations s).map (relabel (binaryLeft s t)) ++
      (termEquations t).map (relabel (binaryRight s t))) ++
      [sub (atom (.inr (.inl ())))
        (add (atom (.inr (.inr (.inl (termRoot s))))) (atom (.inr (.inr (.inr (termRoot t))))))]
  | .mul s t =>
    ((termEquations s).map (relabel (binaryLeft s t)) ++
      (termEquations t).map (relabel (binaryRight s t))) ++
      [sub (atom (.inr (.inl ())))
        (product (atom (.inr (.inr (.inl (termRoot s))))) (atom (.inr (.inr (.inr (termRoot t))))))]
  | .neg s =>
    (termEquations s).map (relabel (unaryChild s)) ++
      [add (atom (.inr (.inl ()))) (atom (.inr (.inr (termRoot s))))]

theorem term_interpret (t : Term n) :
    (termEquations t).map interpret = QuadraticCircuit.termEquations t := by
  induction t with
  | int z => simp only [termEquations, QuadraticCircuit.termEquations, List.map_cons, List.map_nil,
      interpret_sub, interpret_atom, interpret_constant]
  | var v => simp only [termEquations, QuadraticCircuit.termEquations, List.map_cons, List.map_nil,
      interpret_sub, interpret_atom]
  | add s t hs ht =>
    simp only [termEquations, QuadraticCircuit.termEquations, List.map_append, interpret_relabel_list,
      hs, ht, List.map_cons, List.map_nil, interpret_sub, interpret_atom, interpret_add]
  | mul s t hs ht =>
    simp only [termEquations, QuadraticCircuit.termEquations, List.map_append, interpret_relabel_list,
      hs, ht, List.map_cons, List.map_nil, interpret_sub, interpret_atom, interpret_product]
  | neg s hs =>
    simp only [termEquations, QuadraticCircuit.termEquations, List.map_append, interpret_relabel_list,
      hs, List.map_cons, List.map_nil, interpret_add, interpret_atom]

theorem term_equation_count (t : Term n) : (termEquations t).length = t.size := by
  have h := congrArg List.length (term_interpret t)
  simpa only [List.length_map, QuadraticCircuit.termEquations_length] using h

end JointThermoComplexity.Complexity.SparseCircuit

#print axioms JointThermoComplexity.Complexity.SparseCircuit.term_interpret
#print axioms JointThermoComplexity.Complexity.SparseCircuit.term_equation_count
