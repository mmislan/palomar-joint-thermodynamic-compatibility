module
public import proofs.JointThermoComplexity.Complexity.SourcePolynomialSchedules
public import proofs.JointThermoComplexity.Complexity.SparseScaledSource
public import proofs.JointThermoComplexity.Complexity.SparseCirclePadding
public import proofs.JointThermoComplexity.Complexity.SparseStrictPolynomial

set_option autoImplicit false
@[expose] public section

/-! # Executable strict source polynomials with explicit finite integer IDs

Every finite enumeration and both strict polynomial lists are computed from
the source sentence. The semantic bridge separately identifies these light
polynomial schedules with the proved quantitative schedules.
-/

namespace JointThermoComplexity.Complexity.NumericStrictData
open RealSyntax SourceCoordinateEnumeration SourcePolynomialSchedules SparseInteger

abbrev ScaleCoordinates (s : Sentence) := SparseScaledSource.Coordinates s (scaleLength s.code.length)
abbrev ScaleIndices (s : Sentence) := SparseScaledSource.Indices s (scaleLength s.code.length)
abbrev PaddedCoordinates (s : Sentence) := ScaleCoordinates s × Bool
abbrev PaddedIndices (s : Sentence) := ScaleIndices s ⊕ ScaleCoordinates s
abbrev Variables (s : Sentence) := PaddedCoordinates s ⊕ Fin (thresholdLength s.code.length + 1)

def scaleCoordinateCount (s : Sentence) : ℕ := sourceCount s + (scaleLength s.code.length + 1)
def scaleEquationCount (s : Sentence) : ℕ := (NumericSparseSource.equations s).length + (1 + scaleLength s.code.length)
def paddedEquationCount (s : Sentence) : ℕ := scaleEquationCount s + scaleCoordinateCount s
def variableCount (s : Sentence) : ℕ := scaleCoordinateCount s * 2 + (thresholdLength s.code.length + 1)

def scaleCoordinateEnumeration (s : Sentence) : ScaleCoordinates s ≃ Fin (scaleCoordinateCount s) :=
  sumEnumeration (Equiv.refl _) (Equiv.refl _)

def scaleIndexEnumeration (s : Sentence) : ScaleIndices s ≃ Fin (scaleEquationCount s) :=
  sumEnumeration (Equiv.refl _) (sumEnumeration unitEnumeration (Equiv.refl _))

def paddedIndexEnumeration (s : Sentence) : PaddedIndices s ≃ Fin (paddedEquationCount s) :=
  sumEnumeration (scaleIndexEnumeration s) (scaleCoordinateEnumeration s)

def boolEnumeration : Bool ≃ Fin 2 where
  toFun := fun b => if b then 1 else 0
  invFun := fun i => decide (i.val = 1)
  left_inv := fun b => by cases b <;> rfl
  right_inv := fun i => by
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i => omega

def paddedCoordinateEnumeration (s : Sentence) : PaddedCoordinates s ≃ Fin (scaleCoordinateCount s * 2) :=
  (Equiv.prodCongr (scaleCoordinateEnumeration s) boolEnumeration).trans finProdFinEquiv

def variableEnumeration (s : Sentence) : Variables s ≃ Fin (variableCount s) :=
  sumEnumeration (paddedCoordinateEnumeration s) (Equiv.refl _)

def paddedFamily (s : Sentence) : PaddedIndices s → Poly (PaddedCoordinates s) :=
  SparseCirclePadding.family (SparseScaledSource.family s (scaleLength s.code.length))

def energyFamily (s : Sentence) (j : Fin (paddedEquationCount s)) : Poly (PaddedCoordinates s) :=
  paddedFamily s ((paddedIndexEnumeration s).symm j)

def boundedUnnumbered (s : Sentence) : Poly (Variables s) :=
  SparseStrictPolynomial.bounded (energyFamily s) (thresholdLength s.code.length)

def allRealUnnumbered (s : Sentence) : Poly (Variables s) :=
  SparseStrictPolynomial.allReal (energyFamily s) (thresholdLength s.code.length)

def bounded (s : Sentence) : Poly (Fin (variableCount s)) := relabel (variableEnumeration s) (boundedUnnumbered s)
def allReal (s : Sentence) : Poly (Fin (variableCount s)) := relabel (variableEnumeration s) (allRealUnnumbered s)

theorem energyFamily_raw_degree (s : Sentence) (j : Fin (paddedEquationCount s)) : DegreeLE 2 (energyFamily s j) :=
  SparseCirclePadding.family_degree _ (SparseScaledSource.family_raw_degree s (scaleLength s.code.length))
    ((paddedIndexEnumeration s).symm j)

theorem bounded_raw_degree (s : Sentence) : DegreeLE 4 (bounded s) :=
  degree_relabel _ (SparseStrictPolynomial.bounded_degree (energyFamily s) (energyFamily_raw_degree s) _)

theorem allReal_raw_degree (s : Sentence) : DegreeLE 4 (allReal s) :=
  degree_relabel _ (SparseStrictPolynomial.allReal_degree (energyFamily s) (energyFamily_raw_degree s) _)

theorem equation_count (s : Sentence) : paddedEquationCount s ≤ 9 * s.code.length + 2 * scaleLength s.code.length + 3 := by
  have hn := NumericSparseSource.coordinate_count s
  have he := NumericSparseSource.equation_count s
  unfold paddedEquationCount scaleEquationCount scaleCoordinateCount
  omega

theorem coordinate_count (s : Sentence) :
    variableCount s ≤ 10 * s.code.length + 2 * scaleLength s.code.length + thresholdLength s.code.length + 3 := by
  have hn := NumericSparseSource.coordinate_count s
  unfold variableCount scaleCoordinateCount
  omega

theorem coordinate_count_polynomial (s : Sentence) :
    variableCount s ≤ 57600 * s.code.length ^ 4 + 518880 * s.code.length ^ 3 +
      1291440 * s.code.length ^ 2 + 553437 * s.code.length + 65225 := by
  calc
    variableCount s ≤ 10 * s.code.length + 2 * scaleLength s.code.length + thresholdLength s.code.length + 3 := coordinate_count s
    _ = _ := by unfold scaleLength thresholdLength; ring

end JointThermoComplexity.Complexity.NumericStrictData

#print axioms JointThermoComplexity.Complexity.NumericStrictData.bounded
#print axioms JointThermoComplexity.Complexity.NumericStrictData.allReal
#print axioms JointThermoComplexity.Complexity.NumericStrictData.variableEnumeration
#print axioms JointThermoComplexity.Complexity.NumericStrictData.bounded_raw_degree
#print axioms JointThermoComplexity.Complexity.NumericStrictData.coordinate_count_polynomial
