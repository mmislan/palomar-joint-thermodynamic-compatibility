module
public import proofs.JointThermoComplexity.Complexity.NumberedTermEquations
public import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false
@[expose] public section

/-! Forward term-equation order with a proved permutation of the accepted numbered data. -/

namespace JointThermoComplexity.Complexity.PreorderTermEquations
open RealSyntax SparseInteger
variable {n : ℕ} {α : Type}

theorem prepend_perm {xs xs' ys ys' : List α} (root : List α) (hx : xs.Perm xs') (hy : ys.Perm ys') :
    (root ++ (xs ++ ys)).Perm ((xs' ++ ys') ++ root) :=
  (List.Perm.append_left root (hx.append hy)).trans List.perm_append_comm

theorem prepend_unary_perm {xs xs' : List α} (root : List α) (hx : xs.Perm xs') :
    (root ++ xs).Perm (xs' ++ root) := (List.Perm.append_left root hx).trans List.perm_append_comm

def equations : (t : Term n) → (Fin n → ℕ) → ℕ → List (Poly ℕ)
  | .int z, _, offset => [sub (atom offset) (constant z)]
  | .var v, inputs, offset => [sub (atom offset) (atom (inputs v))]
  | .add s t, inputs, offset =>
      [sub (atom offset) (add (atom (offset + 1)) (atom (offset + 1 + s.size)))] ++
        (equations s inputs (offset + 1) ++ equations t inputs (offset + 1 + s.size))
  | .mul s t, inputs, offset =>
      [sub (atom offset) (product (atom (offset + 1)) (atom (offset + 1 + s.size)))] ++
        (equations s inputs (offset + 1) ++ equations t inputs (offset + 1 + s.size))
  | .neg s, inputs, offset => [add (atom offset) (atom (offset + 1))] ++ equations s inputs (offset + 1)

theorem perm_numbered (t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    (equations t inputs offset).Perm (NumberedTermEquations.equations t inputs offset) := by
  induction t generalizing offset with
  | int z | var v => exact List.Perm.refl _
  | add s t hs ht | mul s t hs ht => exact prepend_perm _ (hs _) (ht _)
  | neg s hs => exact prepend_unary_perm _ (hs _)

theorem equation_count (t : Term n) (inputs : Fin n → ℕ) (offset : ℕ) :
    (equations t inputs offset).length = t.size :=
  (perm_numbered t inputs offset).length_eq.trans (NumberedTermEquations.equation_count t inputs offset)

end JointThermoComplexity.Complexity.PreorderTermEquations

#print axioms JointThermoComplexity.Complexity.PreorderTermEquations.perm_numbered
#print axioms JointThermoComplexity.Complexity.PreorderTermEquations.equation_count
