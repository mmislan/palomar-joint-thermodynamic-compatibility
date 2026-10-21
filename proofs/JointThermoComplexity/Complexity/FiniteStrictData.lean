module
public import proofs.JointThermoComplexity.Complexity.EquationCodeBounds
public import proofs.JointThermoComplexity.Complexity.NumericStrictData

set_option autoImplicit false
@[expose] public section

/-! Explicit scale, circle and strict integer data from any encoded finite equation system.

Schedules depend on its equation-code length. Their semantic adequacy and the
binary runtime are separate obligations; these definitions contain no witness.
-/

namespace JointThermoComplexity.Complexity.FiniteStrictData
open SparseInteger EquationSystemCodec SourcePolynomialSchedules SourceCoordinateEnumeration

def inputLength (p : Data) : ℕ := (EquationSystemCodec.code p).length
def scaleCount (p : Data) : ℕ := scaleLength (inputLength p)
def thresholdCount (p : Data) : ℕ := thresholdLength (inputLength p)

abbrev OriginalIndices (p : Data) := Fin p.rows.length
abbrev ScaleCoordinates (p : Data) := Fin p.arity ⊕ Fin (scaleCount p + 1)
abbrev ScaleIndices (p : Data) := OriginalIndices p ⊕ (Unit ⊕ Fin (scaleCount p))
abbrev PaddedCoordinates (p : Data) := ScaleCoordinates p × Bool
abbrev PaddedIndices (p : Data) := ScaleIndices p ⊕ ScaleCoordinates p
abbrev Variables (p : Data) := PaddedCoordinates p ⊕ Fin (thresholdCount p + 1)

def original (p : Data) (j : OriginalIndices p) : Poly (Fin p.arity) := p.rows[j.val]'j.isLt

def scaledFamily (p : Data) : ScaleIndices p → Poly (ScaleCoordinates p) :=
  SparseScaledSystem.family (original p) (scaleCount p)

def paddedFamily (p : Data) : PaddedIndices p → Poly (PaddedCoordinates p) :=
  SparseCirclePadding.family (scaledFamily p)

def scaleCoordinateCount (p : Data) : ℕ := p.arity + (scaleCount p + 1)
def scaleEquationCount (p : Data) : ℕ := p.rows.length + (1 + scaleCount p)
def paddedEquationCount (p : Data) : ℕ := scaleEquationCount p + scaleCoordinateCount p
def variableCount (p : Data) : ℕ := scaleCoordinateCount p * 2 + (thresholdCount p + 1)

def scaleCoordinateEnumeration (p : Data) : ScaleCoordinates p ≃ Fin (scaleCoordinateCount p) :=
  sumEnumeration (Equiv.refl _) (Equiv.refl _)

def scaleIndexEnumeration (p : Data) : ScaleIndices p ≃ Fin (scaleEquationCount p) :=
  sumEnumeration (Equiv.refl _) (sumEnumeration unitEnumeration (Equiv.refl _))

def paddedIndexEnumeration (p : Data) : PaddedIndices p ≃ Fin (paddedEquationCount p) :=
  sumEnumeration (scaleIndexEnumeration p) (scaleCoordinateEnumeration p)

def paddedCoordinateEnumeration (p : Data) : PaddedCoordinates p ≃ Fin (scaleCoordinateCount p * 2) :=
  (Equiv.prodCongr (scaleCoordinateEnumeration p) NumericStrictData.boolEnumeration).trans finProdFinEquiv

def variableEnumeration (p : Data) : Variables p ≃ Fin (variableCount p) :=
  sumEnumeration (paddedCoordinateEnumeration p) (Equiv.refl _)

def energyFamily (p : Data) (j : Fin (paddedEquationCount p)) : Poly (PaddedCoordinates p) :=
  paddedFamily p ((paddedIndexEnumeration p).symm j)

def boundedUnnumbered (p : Data) : Poly (Variables p) :=
  SparseStrictPolynomial.bounded (energyFamily p) (thresholdCount p)

def allRealUnnumbered (p : Data) : Poly (Variables p) :=
  SparseStrictPolynomial.allReal (energyFamily p) (thresholdCount p)

def bounded (p : Data) : Poly (Fin (variableCount p)) := relabel (variableEnumeration p) (boundedUnnumbered p)
def allReal (p : Data) : Poly (Fin (variableCount p)) := relabel (variableEnumeration p) (allRealUnnumbered p)

def boundedData (p : Data) : SparsePolynomialCodec.PolynomialData := ⟨variableCount p, bounded p⟩
def allRealData (p : Data) : SparsePolynomialCodec.PolynomialData := ⟨variableCount p, allReal p⟩
def boundedCode (p : Data) : List Bool := SparsePolynomialCodec.code (boundedData p)
def allRealCode (p : Data) : List Bool := SparsePolynomialCodec.code (allRealData p)

theorem bounded_decode (p : Data) : SparsePolynomialCodec.decode (boundedCode p) = some (boundedData p) :=
  SparsePolynomialCodec.decode_code _

theorem allReal_decode (p : Data) : SparsePolynomialCodec.decode (allRealCode p) = some (allRealData p) :=
  SparsePolynomialCodec.decode_code _

theorem original_holds_iff (p : Data) (x : Fin p.arity → ℝ) :
    (∀ j, (interpret (original p j)).eval₂ (Int.castRingHom ℝ) x = 0) ↔
      ∀ q ∈ p.rows, (interpret q).eval₂ (Int.castRingHom ℝ) x = 0 := by
  constructor
  · intro h
    exact List.forall_mem_iff_getElem.mpr (fun i hi => h ⟨i, hi⟩)
  · intro h j
    exact h _ (List.getElem_mem j.isLt)

theorem counts (p : Data) :
    paddedEquationCount p = p.rows.length + p.arity + 2 * scaleCount p + 2 ∧
    variableCount p = 2 * p.arity + 2 * scaleCount p + thresholdCount p + 3 := by
  dsimp [paddedEquationCount, scaleEquationCount, scaleCoordinateCount, variableCount]
  omega

theorem variableCount_pos (p : Data) : 0 < variableCount p := by
  dsimp [variableCount]
  omega

theorem energy_degree (p : Data) (j : Fin (paddedEquationCount p)) : DegreeLE 2 (energyFamily p j) :=
  SparseCirclePadding.family_degree _ (SparseScaledSystem.family_degree (original p) (scaleCount p)) _

theorem bounded_degree (p : Data) : DegreeLE 4 (bounded p) :=
  degree_relabel _ (SparseStrictPolynomial.bounded_degree (energyFamily p) (energy_degree p) _)

theorem allReal_degree (p : Data) : DegreeLE 4 (allReal p) :=
  degree_relabel _ (SparseStrictPolynomial.allReal_degree (energyFamily p) (energy_degree p) _)

end JointThermoComplexity.Complexity.FiniteStrictData

#print axioms JointThermoComplexity.Complexity.FiniteStrictData.variableEnumeration
#print axioms JointThermoComplexity.Complexity.FiniteStrictData.bounded_decode
#print axioms JointThermoComplexity.Complexity.FiniteStrictData.original_holds_iff
#print axioms JointThermoComplexity.Complexity.FiniteStrictData.counts
#print axioms JointThermoComplexity.Complexity.FiniteStrictData.bounded_degree
#print axioms JointThermoComplexity.Complexity.FiniteStrictData.allReal_degree
