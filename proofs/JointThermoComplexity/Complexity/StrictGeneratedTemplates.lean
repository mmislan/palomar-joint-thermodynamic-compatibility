module
public import proofs.JointThermoComplexity.Complexity.WordPolynomialProgram
public import proofs.JointThermoComplexity.Complexity.NumberedTermEquations

set_option autoImplicit false
@[expose] public section

/-! Fixed sparse templates for every generated strict-polynomial section.
Only two raw binary address words are needed. The error chain has weight400;
the padded equations have weight256. All literal Cartesian occurrences remain.
-/

namespace JointThermoComplexity.Complexity.StrictGeneratedTemplates
open SparseInteger WordPolynomialProgram
open NumberedTermEquations

inductive Kind where
  | scaleInitial | scaleEdge | circle | errorInitial | errorEdge | boxedLead | unboxedLead
  deriving DecidableEq

def scaleInitialRow : Poly (Ref 2) := sub (scale 4 (atom (.paired false 0))) (constant 1)
def scaleEdgeRow : Poly (Ref 2) := sub (atom (.paired false 1)) (square (atom (.paired false 0)))
def circleRow : Poly (Ref 2) :=
  sub (scale 16 (add (square (atom (.paired false 0))) (square (atom (.paired true 0))))) (constant 1)
def errorInitialRow : Poly (Ref 2) := sub (scale 16 (atom (.plain 0))) (constant 1)
def errorEdgeRow : Poly (Ref 2) := scale 16 (sub (atom (.plain 1)) (square (atom (.plain 0))))

def template : Kind → Poly (Ref 2)
  | .scaleInitial => scale (-256) (square scaleInitialRow)
  | .scaleEdge => scale (-256) (square scaleEdgeRow)
  | .circle => scale (-256) (square circleRow)
  | .errorInitial => scale (-400) (square errorInitialRow)
  | .errorEdge => scale (-400) (square errorEdgeRow)
  | .boxedLead => scale 256 (square (atom (.plain 0)))
  | .unboxedLead => scale 256 (product (square (atom (.plain 0)))
      (sub (constant 1) (square (atom (.plain 0)))))

def data (values : Fin 2 → ℕ) (kind : Kind) : Poly ℕ := relabel (refValue values) (template kind)

theorem scale_initial_data (values : Fin 2 → ℕ) : data values .scaleInitial =
    scale (-256) (square (sub (scale 4 (atom (2 * values 0))) (constant 1))) := by
  simp only [data, template, scaleInitialRow, relabel_scale, relabel_square, relabel_sub,
    relabel_atom, relabel_constant, refValue, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem scale_edge_data (values : Fin 2 → ℕ) : data values .scaleEdge =
    scale (-256) (square (sub (atom (2 * values 1)) (square (atom (2 * values 0))))) := by
  simp only [data, template, scaleEdgeRow, relabel_scale, relabel_square, relabel_sub,
    relabel_atom, refValue, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem circle_data (values : Fin 2 → ℕ) : data values .circle =
    scale (-256) (square (sub (scale 16 (add (square (atom (2 * values 0)))
      (square (atom (2 * values 0 + 1))))) (constant 1))) := by
  simp only [data, template, circleRow, relabel_scale, relabel_square, relabel_sub,
    relabel_add, relabel_atom, relabel_constant, refValue, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem error_initial_data (values : Fin 2 → ℕ) : data values .errorInitial =
    scale (-400) (square (sub (scale 16 (atom (values 0))) (constant 1))) := by
  simp only [data, template, errorInitialRow, relabel_scale, relabel_square, relabel_sub,
    relabel_atom, relabel_constant, refValue]

theorem error_edge_data (values : Fin 2 → ℕ) : data values .errorEdge =
    scale (-400) (square (scale 16 (sub (atom (values 1)) (square (atom (values 0)))))) := by
  simp only [data, template, errorEdgeRow, relabel_scale, relabel_square, relabel_sub, relabel_atom, refValue]

theorem boxed_lead_data (values : Fin 2 → ℕ) : data values .boxedLead = scale 256 (square (atom (values 0))) := by
  simp only [data, template, relabel_scale, relabel_square, relabel_atom, refValue]

theorem unboxed_lead_data (values : Fin 2 → ℕ) : data values .unboxedLead =
    scale 256 (product (square (atom (values 0))) (sub (constant 1) (square (atom (values 0))))) := by
  simp only [data, template, relabel_scale, relabel_product, relabel_square, relabel_sub,
    relabel_atom, relabel_constant, refValue]

end JointThermoComplexity.Complexity.StrictGeneratedTemplates

#print axioms JointThermoComplexity.Complexity.StrictGeneratedTemplates.scale_initial_data
#print axioms JointThermoComplexity.Complexity.StrictGeneratedTemplates.circle_data
#print axioms JointThermoComplexity.Complexity.StrictGeneratedTemplates.error_edge_data
#print axioms JointThermoComplexity.Complexity.StrictGeneratedTemplates.unboxed_lead_data
