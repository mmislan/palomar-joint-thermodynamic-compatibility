module
public import proofs.JointThermoComplexity.Complexity.SparseQuadraticLift
public import proofs.JointThermoComplexity.Complexity.NumberedTermEquations

set_option autoImplicit false
@[expose] public section

/-! Literal quadratic-lift naturality under variable relabeling. Raw monomial
length, zero coefficients and stored term order are unchanged.
-/

namespace JointThermoComplexity.Complexity.SparseQuadraticRelabel
open SparseInteger
variable {V W : Type}

theorem term (f : V → W) (a : ℤ × List V) :
    SparseQuadraticLift.term (a.1, a.2.map f) =
      relabel (Sum.map f id) (SparseQuadraticLift.term a) := by
  unfold SparseQuadraticLift.term
  simp only [List.length_map]
  split_ifs <;> simp [relabel, List.map_map, Function.comp_def]

theorem lift (f : V → W) (p : Poly V) :
    SparseQuadraticLift.lift (relabel f p) = relabel (Sum.map f id) (SparseQuadraticLift.lift p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change SparseQuadraticLift.term (a.1, a.2.map f) ++ SparseQuadraticLift.lift (relabel f p) = _
    rw [term, ih]
    simp only [SparseQuadraticLift.lift, List.flatMap_cons, relabel, List.map_append]

end JointThermoComplexity.Complexity.SparseQuadraticRelabel

#print axioms JointThermoComplexity.Complexity.SparseQuadraticRelabel.term
#print axioms JointThermoComplexity.Complexity.SparseQuadraticRelabel.lift
