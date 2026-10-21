module
public import proofs.JointThermoComplexity.Complexity.FiniteStrictData

set_option autoImplicit false
@[expose] public section

/-! Exact values of the executable finite strict coordinate and equation
enumerations. Original rows, scale equations and circles keep their literal order.
-/

namespace JointThermoComplexity.Complexity.FiniteStrictNumbering
open EquationSystemCodec FiniteStrictData

def coordinateVariable (p : Data) (c : ScaleCoordinates p) (b : Bool) : Fin (variableCount p) := variableEnumeration p (.inl (c, b))
def originalVariable (p : Data) (v : Fin p.arity) : Fin (variableCount p) := coordinateVariable p (.inl v) false
def scaleVariable (p : Data) (j : Fin (scaleCount p + 1)) : Fin (variableCount p) := coordinateVariable p (.inr j) false
def sharedScale (p : Data) : Fin (variableCount p) := scaleVariable p (Fin.last (scaleCount p))
def errorVariable (p : Data) (j : Fin (thresholdCount p + 1)) : Fin (variableCount p) := variableEnumeration p (.inr j)

theorem scale_original_val (p : Data) (v : Fin p.arity) : (scaleCoordinateEnumeration p (.inl v)).val = v.val := rfl
theorem scale_chain_val (p : Data) (j : Fin (scaleCount p + 1)) : (scaleCoordinateEnumeration p (.inr j)).val = p.arity + j.val := rfl

theorem variable_val (p : Data) (c : ScaleCoordinates p) (b : Bool) :
    (coordinateVariable p c b).val = 2 * (scaleCoordinateEnumeration p c).val + if b then 1 else 0 := by
  cases b with
  | false =>
    change 0 + 2 * (scaleCoordinateEnumeration p c).val = 2 * (scaleCoordinateEnumeration p c).val + 0
    omega
  | true =>
    change 1 + 2 * (scaleCoordinateEnumeration p c).val = 2 * (scaleCoordinateEnumeration p c).val + 1
    omega

theorem original_val (p : Data) (v : Fin p.arity) : (originalVariable p v).val = 2 * v.val := by
  rw [originalVariable, variable_val, scale_original_val]
  rfl

theorem scale_val (p : Data) (j : Fin (scaleCount p + 1)) : (scaleVariable p j).val = 2 * (p.arity + j.val) := by
  rw [scaleVariable, variable_val, scale_chain_val]
  rfl

theorem shared_val (p : Data) : (sharedScale p).val = 2 * (p.arity + scaleCount p) := scale_val p (Fin.last (scaleCount p))

theorem error_val (p : Data) (j : Fin (thresholdCount p + 1)) :
    (errorVariable p j).val = scaleCoordinateCount p * 2 + j.val := rfl

def originalIndex (p : Data) (i : OriginalIndices p) : Fin (paddedEquationCount p) := paddedIndexEnumeration p (.inl (.inl i))
def scaleInitialIndex (p : Data) : Fin (paddedEquationCount p) := paddedIndexEnumeration p (.inl (.inr (.inl ())))
def scaleEdgeIndex (p : Data) (j : Fin (scaleCount p)) : Fin (paddedEquationCount p) := paddedIndexEnumeration p (.inl (.inr (.inr j)))
def circleIndex (p : Data) (c : ScaleCoordinates p) : Fin (paddedEquationCount p) := paddedIndexEnumeration p (.inr c)

theorem original_index_val (p : Data) (i : OriginalIndices p) : (originalIndex p i).val = i.val := rfl
theorem scale_initial_val (p : Data) : (scaleInitialIndex p).val = p.rows.length := by
  change p.rows.length + 0 = p.rows.length
  rfl
theorem scale_edge_val (p : Data) (j : Fin (scaleCount p)) : (scaleEdgeIndex p j).val = p.rows.length + 1 + j.val := by
  change p.rows.length + (1 + j.val) = _
  omega
theorem circle_val (p : Data) (c : ScaleCoordinates p) :
    (circleIndex p c).val = scaleEquationCount p + (scaleCoordinateEnumeration p c).val := rfl

theorem original_energy (p : Data) (i : OriginalIndices p) :
    energyFamily p (originalIndex p i) = paddedFamily p (.inl (.inl i)) := by
  simp only [energyFamily, originalIndex, Equiv.symm_apply_apply]
theorem scale_initial_energy (p : Data) : energyFamily p (scaleInitialIndex p) = paddedFamily p (.inl (.inr (.inl ()))) := by
  simp only [energyFamily, scaleInitialIndex, Equiv.symm_apply_apply]
theorem scale_edge_energy (p : Data) (j : Fin (scaleCount p)) :
    energyFamily p (scaleEdgeIndex p j) = paddedFamily p (.inl (.inr (.inr j))) := by
  simp only [energyFamily, scaleEdgeIndex, Equiv.symm_apply_apply]
theorem circle_energy (p : Data) (c : ScaleCoordinates p) : energyFamily p (circleIndex p c) = paddedFamily p (.inr c) := by
  simp only [energyFamily, circleIndex, Equiv.symm_apply_apply]

end JointThermoComplexity.Complexity.FiniteStrictNumbering

#print axioms JointThermoComplexity.Complexity.FiniteStrictNumbering.variable_val
#print axioms JointThermoComplexity.Complexity.FiniteStrictNumbering.shared_val
#print axioms JointThermoComplexity.Complexity.FiniteStrictNumbering.original_energy
