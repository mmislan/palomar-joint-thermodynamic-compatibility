module
public import proofs.JointThermoComplexity.Complexity.PreorderSourceEquations
public import proofs.JointThermoComplexity.Complexity.EquationVariableCount

set_option autoImplicit false
@[expose] public section

/-! Finite indices for the exact preorder stream. The total fallback is unused on emitted coordinates. -/

namespace JointThermoComplexity.Complexity.FinitePreorderEquations
open RealSyntax SparseInteger SourceCoordinateEnumeration

def index (s : Sentence) (v : ℕ) : Fin (sourceCount s) :=
  if h : v < sourceCount s then ⟨v, h⟩ else ⟨0, EquationVariableCount.sourceCount_pos s⟩

@[simp] theorem index_fin (s : Sentence) (v : Fin (sourceCount s)) : index s v.val = v := by
  simp [index, v.isLt]

theorem index_val (s : Sentence) (v : ℕ) (hv : v < sourceCount s) : (index s v).val = v := by
  simp [index, hv]

def equations (s : Sentence) : List (Poly (Fin (sourceCount s))) :=
  (PreorderSourceEquations.equations s).map (relabel (index s))

theorem finite_roundtrip (s : Sentence) (p : Poly (Fin (sourceCount s))) :
    relabel (index s) (relabel Fin.val p) = p := by
  simp [relabel, List.map_map, Function.comp_def]

theorem row_roundtrip (s : Sentence) (p : Poly ℕ) (hp : p ∈ PreorderSourceEquations.equations s) :
    relabel Fin.val (relabel (index s) p) = p := by
  rw [NumberedTermEquations.relabel_comp]
  unfold relabel
  conv_rhs => rw [← List.map_id p]
  apply List.map_congr_left
  intro a ha
  change (a.1, a.2.map (Fin.val ∘ index s)) = (a.1, a.2)
  have h : a.2.map (Fin.val ∘ index s) = a.2.map id := by
    apply List.map_congr_left
    intro v hv
    exact index_val s v (PreorderSourceEquations.coordinate_bound s p hp a ha v hv)
  simpa only [List.map_id] using congrArg (fun vs => (a.1, vs)) h

theorem natural_rows (s : Sentence) :
    (equations s).map (relabel Fin.val) = PreorderSourceEquations.equations s := by
  rw [equations, List.map_map]
  conv_rhs => rw [← List.map_id (PreorderSourceEquations.equations s)]
  apply List.map_congr_left
  intro p hp
  exact row_roundtrip s p hp

theorem perm_numeric (s : Sentence) : (equations s).Perm (NumericSparseSource.equations s) := by
  have h := (PreorderSourceEquations.perm_numbered s).map (relabel (index s))
  rw [← NumberedSourceEquations.equations_agree] at h
  simpa [equations, List.map_map, Function.comp_def, finite_roundtrip] using h

theorem equation_count (s : Sentence) : (equations s).length ≤ 4 * s.code.length + 1 := by
  simpa only [equations, List.length_map] using PreorderSourceEquations.equation_count_bound s

end JointThermoComplexity.Complexity.FinitePreorderEquations

#print axioms JointThermoComplexity.Complexity.FinitePreorderEquations.natural_rows
#print axioms JointThermoComplexity.Complexity.FinitePreorderEquations.perm_numeric
