module
public import proofs.JointThermoComplexity.Complexity.FiniteStrictData
public import proofs.JointThermoComplexity.Complexity.FiniteEquationHardness
public import proofs.JointThermoComplexity.Complexity.SmallStrictMaps

set_option autoImplicit false
@[expose] public section

/-! Raw bounds of the finite-system strict data. These bound the actual stored
terms and coefficient encodings, independently of polynomial cancellation.
They do not assert semantic adequacy of the schedules or binary runtime.
-/

namespace JointThermoComplexity.Complexity.FiniteStrictBounds
open SparseInteger EquationSystemCodec FiniteStrictData SourcePolynomialSchedules

theorem original_length (p : Data) (hp : FiniteEquationHardness.Domain p) (j : OriginalIndices p) :
    (original p j).length ≤ 3 := (hp.2 _ (List.getElem_mem j.isLt)).1.1

theorem original_weight (p : Data) (hp : FiniteEquationHardness.Domain p) (j : OriginalIndices p) :
    rawWeight (original p j) ≤ 5 := (hp.2 _ (List.getElem_mem j.isLt)).1.2

theorem scaled_length (p : Data) (hp : FiniteEquationHardness.Domain p) (j : ScaleIndices p) :
    (scaledFamily p j).length ≤ 3 :=
  SparseScaledSystem.family_length (original p) 3 (original_length p hp) _ j

theorem scaled_weight (p : Data) (hp : FiniteEquationHardness.Domain p) (j : ScaleIndices p) :
    rawWeight (scaledFamily p j) ≤ 5 :=
  SparseRawPipelineBounds.scaled_weight (original p) 5 (original_weight p hp) _ j

theorem padded_length (p : Data) (hp : FiniteEquationHardness.Domain p) (j : PaddedIndices p) :
    (paddedFamily p j).length ≤ 3 := SparseCirclePadding.family_length _ 3 (scaled_length p hp) j

theorem padded_weight (p : Data) (hp : FiniteEquationHardness.Domain p) (j : PaddedIndices p) :
    rawWeight (paddedFamily p j) ≤ 33 := SparseRawPipelineBounds.padded_weight _ 5 (scaled_weight p hp) j

theorem energy_length (p : Data) (hp : FiniteEquationHardness.Domain p) (j : Fin (paddedEquationCount p)) :
    (energyFamily p j).length ≤ 3 := padded_length p hp ((paddedIndexEnumeration p).symm j)

theorem energy_weight (p : Data) (hp : FiniteEquationHardness.Domain p) (j : Fin (paddedEquationCount p)) :
    rawWeight (energyFamily p j) ≤ 33 := padded_weight p hp ((paddedIndexEnumeration p).symm j)

theorem bounded_coefficients (p : Data) (hp : FiniteEquationHardness.Domain p) :
    CoefficientsLE 409600 (bounded p) :=
  coefficients_relabel _ (SparseStrictPolynomial.bounded_fixed_coefficients _ _ (energy_weight p hp))

theorem allReal_coefficients (p : Data) (hp : FiniteEquationHardness.Domain p) :
    CoefficientsLE 409600 (allReal p) :=
  coefficients_relabel _ (SparseStrictPolynomial.allReal_fixed_coefficients _ _ (energy_weight p hp))

theorem bounded_coefficient_code (p : Data) (hp : FiniteEquationHardness.Domain p)
    (a : ℤ × List (Fin (variableCount p))) (ha : a ∈ bounded p) : (BitCodec.integerCode a.1).length ≤ 40 :=
  SmallStrictMaps.fixed_coefficient_code (bounded_coefficients p hp a ha)

theorem allReal_coefficient_code (p : Data) (hp : FiniteEquationHardness.Domain p)
    (a : ℤ × List (Fin (variableCount p))) (ha : a ∈ allReal p) : (BitCodec.integerCode a.1).length ≤ 40 :=
  SmallStrictMaps.fixed_coefficient_code (allReal_coefficients p hp a ha)

def coordinateBound (L : ℕ) : ℕ := 2 * L + 2 * scaleLength L + thresholdLength L + 3
def termCountBound (L : ℕ) : ℕ := 2 + 9 * (2 * L + 2 * scaleLength L + 2) + 4 * (thresholdLength L + 1)
def sizeBound (L : ℕ) : ℕ := coordinateBound L + 2 + termCountBound L * (8 * coordinateBound L + 50)

theorem padded_count (p : Data) : paddedEquationCount p ≤ 2 * inputLength p + 2 * scaleCount p + 2 := by
  have hn := EquationCodeBounds.arity_le_length p
  have hm := EquationCodeBounds.rows_le_length p
  have hc := (counts p).1
  change p.arity ≤ inputLength p at hn
  change p.rows.length ≤ inputLength p at hm
  omega

theorem coordinate_count (p : Data) : variableCount p ≤ coordinateBound (inputLength p) := by
  have hn := EquationCodeBounds.arity_le_length p
  have hc := (counts p).2
  change p.arity ≤ inputLength p at hn
  dsimp [coordinateBound, scaleCount, thresholdCount] at *
  omega

theorem bounded_term_count (p : Data) (hp : FiniteEquationHardness.Domain p) :
    (bounded p).length ≤ termCountBound (inputLength p) := by
  have h := SparseStrictPolynomial.bounded_length (energyFamily p) 3 (energy_length p hp) (thresholdCount p)
  change (boundedUnnumbered p).length ≤ _ at h
  have hc := padded_count p
  simp only [bounded, length_relabel]
  dsimp [termCountBound, scaleCount, thresholdCount] at *
  omega

theorem allReal_term_count (p : Data) (hp : FiniteEquationHardness.Domain p) :
    (allReal p).length ≤ termCountBound (inputLength p) := by
  have h := SparseStrictPolynomial.allReal_length (energyFamily p) 3 (energy_length p hp) (thresholdCount p)
  change (allRealUnnumbered p).length ≤ _ at h
  have hc := padded_count p
  simp only [allReal, length_relabel]
  dsimp [termCountBound, scaleCount, thresholdCount] at *
  omega

theorem polynomial_code_length (p : Data) (q : Poly (Fin (variableCount p))) (hD : DegreeLE 4 q)
    (hC : ∀ a ∈ q, (BitCodec.integerCode a.1).length ≤ 40) (hM : q.length ≤ termCountBound (inputLength p)) :
    (SparsePolynomialCodec.code ⟨variableCount p, q⟩).length ≤ sizeBound (inputLength p) := by
  have h := SparsePolynomialCodec.code_length ⟨variableCount p, q⟩ 4 40 hD hC
  have hn := coordinate_count p
  have hf : 40 + 4 * (2 * variableCount p + 2) + 2 ≤ 8 * coordinateBound (inputLength p) + 50 := by omega
  have hm := Nat.mul_le_mul hM hf
  exact h.trans (Nat.add_le_add (Nat.add_le_add_right hn 2) hm)

theorem boundedCode_length (p : Data) (hp : FiniteEquationHardness.Domain p) :
    (boundedCode p).length ≤ sizeBound (inputLength p) :=
  polynomial_code_length p _ (bounded_degree p) (bounded_coefficient_code p hp) (bounded_term_count p hp)

theorem allRealCode_length (p : Data) (hp : FiniteEquationHardness.Domain p) :
    (allRealCode p).length ≤ sizeBound (inputLength p) :=
  polynomial_code_length p _ (allReal_degree p) (allReal_coefficient_code p hp) (allReal_term_count p hp)

noncomputable def scalePolynomial : Polynomial ℕ := 60 * Polynomial.X ^ 2 + 265 * Polynomial.X + 58
noncomputable def thresholdPolynomial : Polynomial ℕ :=
  57600 * Polynomial.X ^ 4 + 518880 * Polynomial.X ^ 3 + 1291320 * Polynomial.X ^ 2 + 552897 * Polynomial.X + 65106
noncomputable def coordinatePolynomial : Polynomial ℕ := 2 * Polynomial.X + 2 * scalePolynomial + thresholdPolynomial + 3
noncomputable def termPolynomial : Polynomial ℕ :=
  2 + 9 * (2 * Polynomial.X + 2 * scalePolynomial + 2) + 4 * (thresholdPolynomial + 1)
noncomputable def sizePolynomial : Polynomial ℕ :=
  coordinatePolynomial + 2 + termPolynomial * (8 * coordinatePolynomial + 50)

theorem scalePolynomial_eval (L : ℕ) : scalePolynomial.eval L = scaleLength L := by simp [scalePolynomial, scaleLength]
theorem thresholdPolynomial_eval (L : ℕ) : thresholdPolynomial.eval L = thresholdLength L := by
  simp [thresholdPolynomial, thresholdLength]

theorem sizePolynomial_eval (L : ℕ) : sizePolynomial.eval L = sizeBound L := by
  simp [sizePolynomial, coordinatePolynomial, termPolynomial, coordinateBound, termCountBound, sizeBound,
    scalePolynomial_eval, thresholdPolynomial_eval]

theorem boundedCode_polynomial_output (p : Data) (hp : FiniteEquationHardness.Domain p) :
    (boundedCode p).length ≤ sizePolynomial.eval (inputLength p) := by
  rw [sizePolynomial_eval]
  exact boundedCode_length p hp

theorem allRealCode_polynomial_output (p : Data) (hp : FiniteEquationHardness.Domain p) :
    (allRealCode p).length ≤ sizePolynomial.eval (inputLength p) := by
  rw [sizePolynomial_eval]
  exact allRealCode_length p hp

end JointThermoComplexity.Complexity.FiniteStrictBounds

#print axioms JointThermoComplexity.Complexity.FiniteStrictBounds.energy_weight
#print axioms JointThermoComplexity.Complexity.FiniteStrictBounds.bounded_coefficients
#print axioms JointThermoComplexity.Complexity.FiniteStrictBounds.allReal_coefficients
#print axioms JointThermoComplexity.Complexity.FiniteStrictBounds.boundedCode_polynomial_output
#print axioms JointThermoComplexity.Complexity.FiniteStrictBounds.allRealCode_polynomial_output
