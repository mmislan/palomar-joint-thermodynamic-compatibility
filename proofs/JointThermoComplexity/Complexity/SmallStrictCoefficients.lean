module
public import proofs.JointThermoComplexity.Complexity.SourceSmallLiteralSentence
public import proofs.JointThermoComplexity.Complexity.SparseStoredCoefficients

set_option autoImplicit false
@[expose] public section

/-! The actual numbered strict outputs from the normalized source have fixed
stored coefficient magnitude, even on malformed original words. -/

namespace JointThermoComplexity.Complexity.SmallStrictCoefficients
open RealSyntax SourceSmallLiterals SparseInteger SparseRawPipelineBounds
open NumericStrictData SourcePolynomialSchedules

theorem original_weight (s : Sentence) (hs : s.formula.literalHeight ≤ 2)
    (j : SparseScaledSource.OriginalIndices s) : rawWeight (SparseScaledSource.original s j) ≤ 5 := by
  have h := (SparseCircuit.numeric_raw_bound s _ (List.getElem_mem j.isLt)).2
  exact Nat.le_trans h (by omega)

theorem padded_weight (s : Sentence) (hs : s.formula.literalHeight ≤ 2) (j : PaddedIndices s) :
    rawWeight (paddedFamily s j) ≤ 33 := by
  have hscaled (i : SparseScaledSource.Indices s (scaleLength s.code.length)) :
      rawWeight (SparseScaledSource.family s (scaleLength s.code.length) i) ≤ 5 := by
    exact scaled_weight (SparseScaledSource.original s) 5 (original_weight s hs) _ i
  exact SparseRawPipelineBounds.padded_weight _ 5 hscaled j

theorem energy_weight (s : Sentence) (hs : s.formula.literalHeight ≤ 2) (j : Fin (paddedEquationCount s)) :
    rawWeight (energyFamily s j) ≤ 33 := padded_weight s hs ((paddedIndexEnumeration s).symm j)

theorem bounded_coefficients (s : Sentence) (hs : s.formula.literalHeight ≤ 2) :
    CoefficientsLE 409600 (NumericStrictData.bounded s) :=
  coefficients_relabel _ (SparseStrictPolynomial.bounded_fixed_coefficients _ _ (energy_weight s hs))

theorem allReal_coefficients (s : Sentence) (hs : s.formula.literalHeight ≤ 2) :
    CoefficientsLE 409600 (NumericStrictData.allReal s) :=
  coefficients_relabel _ (SparseStrictPolynomial.allReal_fixed_coefficients _ _ (energy_weight s hs))

theorem bounded_normalized (input : List Bool) : CoefficientsLE 409600 (NumericStrictData.bounded (normalizeSmall input)) :=
  bounded_coefficients _ (normalizeSmall_height input)

theorem allReal_normalized (input : List Bool) : CoefficientsLE 409600 (NumericStrictData.allReal (normalizeSmall input)) :=
  allReal_coefficients _ (normalizeSmall_height input)

end JointThermoComplexity.Complexity.SmallStrictCoefficients

#print axioms JointThermoComplexity.Complexity.SmallStrictCoefficients.energy_weight
#print axioms JointThermoComplexity.Complexity.SmallStrictCoefficients.bounded_normalized
#print axioms JointThermoComplexity.Complexity.SmallStrictCoefficients.allReal_normalized
