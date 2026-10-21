module
public import proofs.JointThermoComplexity.Complexity.SmallStrictCoefficients
public import proofs.JointThermoComplexity.Complexity.SourceTotalData

set_option autoImplicit false
@[expose] public section

/-! Total strict maps with fixed coefficient width. Coordinate arithmetic stays
polynomially bounded; no machine-runtime claim follows from these size bounds. -/

namespace JointThermoComplexity.Complexity.SmallStrictMaps
open RealSyntax SourceSmallLiterals SparseInteger SparsePolynomialCodec
open RawSourceMagnitude NumericStrictRawBounds

theorem fixed_coefficient_code {z : ℤ} (hz : z.natAbs ≤ 409600) : (BitCodec.integerCode z).length ≤ 40 := by
  have hbits : z.natAbs.bits.length ≤ 19 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    exact Nat.lt_of_le_of_lt hz (by norm_num : 409600 < 2 ^ 19)
  rw [BitCodec.integerCode_length]
  omega

#print axioms fixed_coefficient_code

def boundedMap (input : List Bool) : List Bool := boundedCode (normalizeSmall input)
def allRealMap (input : List Bool) : List Bool := allRealCode (normalizeSmall input)

theorem boundedMap_decode (input : List Bool) :
    decode (boundedMap input) = some (boundedData (normalizeSmall input)) := decode_code _

theorem allRealMap_decode (input : List Bool) :
    decode (allRealMap input) = some (allRealData (normalizeSmall input)) := decode_code _

theorem bounded_coefficient_code (input : List Bool) (a : ℤ × List (Fin (NumericStrictData.variableCount (normalizeSmall input))))
    (ha : a ∈ NumericStrictData.bounded (normalizeSmall input)) : (BitCodec.integerCode a.1).length ≤ 40 :=
  fixed_coefficient_code (SmallStrictCoefficients.bounded_normalized input a ha)

theorem allReal_coefficient_code (input : List Bool) (a : ℤ × List (Fin (NumericStrictData.variableCount (normalizeSmall input))))
    (ha : a ∈ NumericStrictData.allReal (normalizeSmall input)) : (BitCodec.integerCode a.1).length ≤ 40 :=
  fixed_coefficient_code (SmallStrictCoefficients.allReal_normalized input a ha)

def fixedSizeBound (L : ℕ) : ℕ := coordinateBound L + 2 + termCountBound L * (8 * coordinateBound L + 50)

theorem fixed_source_code_length (s : Sentence) (p : Poly (Fin (NumericStrictData.variableCount s)))
    (hD : DegreeLE 4 p) (hC : ∀ a ∈ p, (BitCodec.integerCode a.1).length ≤ 40)
    (hM : p.length ≤ termCountBound s.code.length) :
    (code ⟨NumericStrictData.variableCount s, p⟩).length ≤ fixedSizeBound s.code.length := by
  have h := code_length (⟨NumericStrictData.variableCount s, p⟩ : PolynomialData) 4 40 hD hC
  have hn := coordinate_count s
  have hf : 40 + 4 * (2 * NumericStrictData.variableCount s + 2) + 2 ≤ 8 * coordinateBound s.code.length + 50 := by omega
  have hm := Nat.mul_le_mul hM hf
  exact Nat.le_trans h (Nat.add_le_add (Nat.add_le_add_right hn 2) hm)

noncomputable def fixedSizePolynomial : Polynomial ℕ :=
  coordinatePolynomial + 2 + termPolynomial * (8 * coordinatePolynomial + 50)

theorem fixedSizePolynomial_eval (L : ℕ) : fixedSizePolynomial.eval L = fixedSizeBound L := by
  simp [fixedSizePolynomial, fixedSizeBound, coordinatePolynomial, termPolynomial,
    coordinateBound, termCountBound_formula]

theorem fixedSizeBound_mono {a b : ℕ} (h : a ≤ b) : fixedSizeBound a ≤ fixedSizeBound b := by
  rw [← fixedSizePolynomial_eval a, ← fixedSizePolynomial_eval b]
  exact SourceTotalData.natPolynomial_eval_mono _ h

theorem boundedMap_length (input : List Bool) : (boundedMap input).length ≤ fixedSizeBound (11 * (input.length + 4)) := by
  have h := fixed_source_code_length (normalizeSmall input) _ (NumericStrictData.bounded_raw_degree _)
    (bounded_coefficient_code input) (bounded_term_count _)
  exact Nat.le_trans h (fixedSizeBound_mono (normalizeSmall_code_length input))

theorem allRealMap_length (input : List Bool) : (allRealMap input).length ≤ fixedSizeBound (11 * (input.length + 4)) := by
  have h := fixed_source_code_length (normalizeSmall input) _ (NumericStrictData.allReal_raw_degree _)
    (allReal_coefficient_code input) (allReal_term_count _)
  exact Nat.le_trans h (fixedSizeBound_mono (normalizeSmall_code_length input))

noncomputable def outputPolynomial : Polynomial ℕ := fixedSizePolynomial.comp (11 * (Polynomial.X + 4))

theorem outputPolynomial_eval (L : ℕ) : outputPolynomial.eval L = fixedSizeBound (11 * (L + 4)) := by
  simp [outputPolynomial, Polynomial.eval_comp, fixedSizePolynomial_eval]

theorem boundedMap_polynomial_output (input : List Bool) : (boundedMap input).length ≤ outputPolynomial.eval input.length := by
  rw [outputPolynomial_eval]
  exact boundedMap_length input

theorem allRealMap_polynomial_output (input : List Bool) : (allRealMap input).length ≤ outputPolynomial.eval input.length := by
  rw [outputPolynomial_eval]
  exact allRealMap_length input

end JointThermoComplexity.Complexity.SmallStrictMaps

#print axioms JointThermoComplexity.Complexity.SmallStrictMaps.fixed_coefficient_code
#print axioms JointThermoComplexity.Complexity.SmallStrictMaps.boundedMap_decode
#print axioms JointThermoComplexity.Complexity.SmallStrictMaps.allRealMap_decode
#print axioms JointThermoComplexity.Complexity.SmallStrictMaps.boundedMap_polynomial_output
#print axioms JointThermoComplexity.Complexity.SmallStrictMaps.allRealMap_polynomial_output
