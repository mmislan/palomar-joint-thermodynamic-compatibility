module
public import proofs.JointThermoComplexity.Complexity.PreorderTermEquations
public import proofs.JointThermoComplexity.Complexity.NumberedFormulaEquations

set_option autoImplicit false
@[expose] public section

/-! Formula equations in forward traversal order, with unchanged numbered coordinates and root activation. -/

namespace JointThermoComplexity.Complexity.PreorderFormulaEquations
open RealSyntax SparseInteger SourceCoordinateEnumeration PreorderTermEquations
open NumberedFormulaEquations (equalityPorts signPorts)
variable {n : ℕ}

def equations : (p : Formula n) → (Fin n → ℕ) → ℕ → List (Poly ℕ)
  | .truth, _, offset => [product (atom offset) (sub (atom offset) (constant 1))]
  | .falsity, _, offset => [atom offset]
  | .eq s t, inputs, offset =>
      SparseCircuit.equalityActivation.map (relabel (equalityPorts offset (offset + 1) (offset + 1 + s.size))) ++
        (PreorderTermEquations.equations s inputs (offset + 1) ++
          PreorderTermEquations.equations t inputs (offset + 1 + s.size))
  | .lt s t, inputs, offset =>
      SparseCircuit.strictSign.map (relabel (signPorts offset (offset + 1) (offset + 1 + s.size)
        (offset + 1 + s.size + t.size))) ++
        (PreorderTermEquations.equations s inputs (offset + 1) ++
          PreorderTermEquations.equations t inputs (offset + 1 + s.size))
  | .conj p q, inputs, offset =>
      [product (atom offset) (sub (atom offset) (constant 1)),
        sub (atom (offset + 1)) (atom offset), sub (atom (offset + 1 + formulaCount p)) (atom offset)] ++
        (equations p inputs (offset + 1) ++ equations q inputs (offset + 1 + formulaCount p))
  | .disj p q, inputs, offset =>
      [product (atom offset) (sub (atom offset) (constant 1)),
        sub (add (atom (offset + 1)) (atom (offset + 1 + formulaCount p))) (atom offset)] ++
        (equations p inputs (offset + 1) ++ equations q inputs (offset + 1 + formulaCount p))

theorem perm_numbered (p : Formula n) (inputs : Fin n → ℕ) (offset : ℕ) :
    (equations p inputs offset).Perm (NumberedFormulaEquations.equations p inputs offset) := by
  induction p generalizing offset with
  | truth | falsity => exact List.Perm.refl _
  | eq s t | lt s t => exact prepend_perm _ (PreorderTermEquations.perm_numbered s inputs _) (PreorderTermEquations.perm_numbered t inputs _)
  | conj p q hp hq | disj p q hp hq => exact prepend_perm _ (hp _) (hq _)

def closed (p : Formula n) (inputs : Fin n → ℕ) (offset : ℕ) : List (Poly ℕ) :=
  equations p inputs offset ++ [sub (atom offset) (constant 1)]

theorem closed_perm (p : Formula n) (inputs : Fin n → ℕ) (offset : ℕ) :
    (closed p inputs offset).Perm (NumberedFormulaEquations.closed p inputs offset) :=
  List.Perm.append_right _ (perm_numbered p inputs offset)

end JointThermoComplexity.Complexity.PreorderFormulaEquations

#print axioms JointThermoComplexity.Complexity.PreorderFormulaEquations.perm_numbered
#print axioms JointThermoComplexity.Complexity.PreorderFormulaEquations.closed_perm
