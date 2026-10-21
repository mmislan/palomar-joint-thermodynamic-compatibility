module
public import proofs.JointThermoComplexity.Complexity.GeneratedEnergyLoop
public import proofs.JointThermoComplexity.Complexity.FiniteStrictSections

set_option autoImplicit false
@[expose] public section

/-! Exact finite meanings of generated-loop address sequences and output.
The second circle buffer advances too, but its value is unused by that template.
-/

namespace JointThermoComplexity.Complexity.FiniteGeneratedLoopData
open SparseInteger EquationSystemCodec FiniteStrictData FiniteStrictNumbering FiniteGeneratedEnergy
open StrictGeneratedTemplates GeneratedEnergyLoop

def scaleValues (p : Data) : Fin 2 → ℕ := ![p.arity, p.arity + 1]
def circleValues : Fin 2 → ℕ := ![0, 0]
def errorValues (p : Data) : Fin 2 → ℕ := ![scaleCoordinateCount p * 2, scaleCoordinateCount p * 2 + 1]

theorem scale_at (p : Data) (j : Fin (scaleCount p)) :
    valuesAt (scaleValues p) j.val = scaleEdgeValues p j := by
  funext i
  fin_cases i
  · rfl
  · change (p.arity + 1) + j.val = p.arity + (j.val + 1)
    omega

theorem error_at (p : Data) (j : Fin (thresholdCount p)) :
    valuesAt (errorValues p) j.val = errorEdgeValues p j := by
  funext i
  fin_cases i
  · rfl
  · change (scaleCoordinateCount p * 2 + 1) + j.val = scaleCoordinateCount p * 2 + (j.val + 1)
    omega

theorem scale_data (p : Data) (j : Fin (scaleCount p)) :
    data (valuesAt (scaleValues p) j.val) .scaleEdge = relabel Fin.val (paddedContribution p (scaleEdgeIndex p j)) := by
  rw [scale_at]
  exact FiniteGeneratedEnergy.scale_edge_data p j

theorem error_data (p : Data) (j : Fin (thresholdCount p)) :
    data (valuesAt (errorValues p) j.val) .errorEdge = relabel Fin.val (errorContribution p j.succ) := by
  rw [error_at]
  exact FiniteGeneratedEnergy.error_edge_data p j

theorem circle_data (p : Data) (j : Fin (scaleCoordinateCount p)) :
    data (valuesAt circleValues j.val) .circle = relabel Fin.val (FiniteStrictSections.circles p j) := by
  have h := FiniteGeneratedEnergy.circle_data p ((scaleCoordinateEnumeration p).symm j)
  rw [StrictGeneratedTemplates.circle_data] at h ⊢
  simpa only [FiniteGeneratedEnergy.circleValues, FiniteStrictSections.circles, valuesAt, circleValues,
    Matrix.cons_val_zero, Equiv.apply_symm_apply, Nat.zero_add] using h

theorem scale_initial_data (p : Data) : data (scaleValues p) .scaleInitial =
    relabel Fin.val (paddedContribution p (scaleInitialIndex p)) := by
  have h := FiniteGeneratedEnergy.scale_initial_data p
  rw [StrictGeneratedTemplates.scale_initial_data] at h ⊢
  simpa only [scaleValues, scaleInitialValues, Matrix.cons_val_zero] using h

theorem error_initial_data (p : Data) : data (errorValues p) .errorInitial = relabel Fin.val (errorContribution p 0) := by
  have h := FiniteGeneratedEnergy.error_initial_data p
  rw [StrictGeneratedTemplates.error_initial_data] at h ⊢
  simpa only [errorValues, errorInitialValues, Matrix.cons_val_zero] using h

theorem entries_finite {n count : ℕ} (values : Fin 2 → ℕ) (kind : Kind) (q : Fin count → Poly (Fin n))
    (hdata : ∀ j, data (valuesAt values j.val) kind = relabel Fin.val (q j)) :
    entries values kind count = FiniteRowSquare.finiteEntries (List.ofFn q).flatten := by
  rw [FiniteRowEnergyLoop.finiteEntries_flatten, List.map_ofFn]
  unfold entries
  congr 1
  apply congrArg List.ofFn
  funext j
  exact congrArg RowSquareCanonical.entries (hdata j)

theorem scale_entries (p : Data) : entries (scaleValues p) .scaleEdge (scaleCount p) =
    FiniteRowSquare.finiteEntries (List.ofFn (fun j => paddedContribution p (scaleEdgeIndex p j))).flatten :=
  entries_finite _ _ _ (scale_data p)

theorem error_entries (p : Data) : entries (errorValues p) .errorEdge (thresholdCount p) =
    FiniteRowSquare.finiteEntries (List.ofFn (fun j : Fin (thresholdCount p) => errorContribution p j.succ)).flatten :=
  entries_finite _ _ _ (error_data p)

theorem circle_entries (p : Data) : entries circleValues .circle (scaleCoordinateCount p) =
    FiniteRowSquare.finiteEntries (FiniteStrictSections.circleEnergy p) :=
  entries_finite _ _ _ (circle_data p)

end JointThermoComplexity.Complexity.FiniteGeneratedLoopData

#print axioms JointThermoComplexity.Complexity.FiniteGeneratedLoopData.circle_data
#print axioms JointThermoComplexity.Complexity.FiniteGeneratedLoopData.scale_entries
#print axioms JointThermoComplexity.Complexity.FiniteGeneratedLoopData.error_entries
#print axioms JointThermoComplexity.Complexity.FiniteGeneratedLoopData.circle_entries
