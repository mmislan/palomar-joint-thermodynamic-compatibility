module
public import proofs.JointThermoComplexity.Complexity.FinitePreorderEquations

set_option autoImplicit false
@[expose] public section

/-! Real solutions and uniform bounds of the finite, order-preserving source stream. -/

namespace JointThermoComplexity.Complexity.FiniteEquationSemantics
open RealSyntax SparseInteger SourceCoordinateEnumeration FinitePreorderEquations

def Feasible {n : ℕ} (ps : List (Poly (Fin n))) : Prop :=
  ∃ x : Fin n → ℝ, ∀ p ∈ ps, (interpret p).eval₂ (Int.castRingHom ℝ) x = 0

theorem satisfiable_iff (s : Sentence) : s.Satisfiable ↔ Feasible (equations s) := by
  rw [NumericSparseSource.satisfiable_iff]
  apply exists_congr
  intro x
  constructor
  · intro h p hp
    exact h p ((perm_numeric s).mem_iff.mp hp)
  · intro h p hp
    exact h p ((perm_numeric s).mem_iff.mpr hp)

theorem equation_degree (s : Sentence) (p : Poly (Fin (sourceCount s))) (hp : p ∈ equations s) :
    (interpret p).totalDegree ≤ 2 :=
  NumericSparseSource.equation_degree s p ((perm_numeric s).mem_iff.mp hp)

theorem raw_bound (s : Sentence) (p : Poly (Fin (sourceCount s))) (hp : p ∈ equations s) :
    SparseCircuit.RawBound (3 + s.formula.literalHeight) p :=
  SparseCircuit.numeric_raw_bound s p ((perm_numeric s).mem_iff.mp hp)

def normalized (input : List Bool) : List (Poly (Fin (EquationVariableCount.count input))) :=
  equations (SourceSmallLiterals.normalizeSmall input)

theorem normalized_satisfiable_iff (input : List Bool) : input ∈ ETR ↔ Feasible (normalized input) :=
  (SourceSmallLiterals.normalizeSmall_satisfiable input).symm.trans (satisfiable_iff _)

theorem normalized_natural_rows (input : List Bool) :
    (normalized input).map (relabel Fin.val) = PreorderSourceEquations.normalized input :=
  natural_rows _

theorem normalized_degree (input : List Bool) (p : Poly (Fin (EquationVariableCount.count input)))
    (hp : p ∈ normalized input) : (interpret p).totalDegree ≤ 2 := equation_degree _ p hp

theorem normalized_raw_bound (input : List Bool) (p : Poly (Fin (EquationVariableCount.count input)))
    (hp : p ∈ normalized input) : SparseCircuit.RawBound 5 p :=
  SparseCircuit.rawBound_mono (by have := SourceSmallLiterals.normalizeSmall_height input; omega) (raw_bound _ p hp)

end JointThermoComplexity.Complexity.FiniteEquationSemantics

#print axioms JointThermoComplexity.Complexity.FiniteEquationSemantics.normalized_satisfiable_iff
#print axioms JointThermoComplexity.Complexity.FiniteEquationSemantics.normalized_degree
#print axioms JointThermoComplexity.Complexity.FiniteEquationSemantics.normalized_raw_bound
