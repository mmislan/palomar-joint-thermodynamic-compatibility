module
public import proofs.JointThermoComplexity.Complexity.SparseRawPipelineBounds
public import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
@[expose] public section

/-! # Raw size bounds for the actual numbered strict polynomials

The coefficient norm and term counts below refer to uncancelled stored lists.
They control serialization input data, without asserting construction runtime.
-/

namespace JointThermoComplexity.Complexity.SparseStrictPolynomial
open SparseInteger
variable {V : Type} {n : ℕ}

theorem rawWeight_flatten (ps : List (Poly V)) : rawWeight ps.flatten = (ps.map rawWeight).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp only [List.flatten_cons, rawWeight_append, List.map_cons, List.sum_cons, ih]

theorem rawWeight_sumFamily (q : Fin n → Poly V) : rawWeight (sumFamily q) = ∑ j, rawWeight (q j) := by
  rw [sumFamily, rawWeight_flatten, List.map_ofFn, List.sum_ofFn]
  rfl

theorem rawWeight_energy (q : Fin n → Poly V) : rawWeight (energy q) = ∑ j, rawWeight (q j) ^ 2 := by
  simp only [energy, rawWeight_sumFamily, rawWeight_square]

theorem energy_weight_le (q : Fin n → Poly V) (B : ℕ) (hB : ∀ j, rawWeight (q j) ≤ B) :
    rawWeight (energy q) ≤ n * B ^ 2 := by
  rw [rawWeight_energy]
  calc
    _ ≤ ∑ _j : Fin n, B ^ 2 := Finset.sum_le_sum (fun j _ => Nat.pow_le_pow_left (hB j) 2)
    _ = _ := by simp

theorem edge_weight (k : ℕ) (i : Fin (k + 1)) : rawWeight (edge k i) ≤ 32 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [edge]
  · simp [edge]

theorem error_weight (k : ℕ) : rawWeight (error k) ≤ (k + 1) * 1024 := by
  have h := energy_weight_le (edge k) 32 (edge_weight k)
  norm_num only at h
  exact h

theorem bounded_weight_le (q : Fin n → Poly V) (B : ℕ) (hB : ∀ j, rawWeight (q j) ≤ B) (k : ℕ) :
    rawWeight (bounded q k) ≤ 256 + 256 * (n * B ^ 2) + 409600 * (k + 1) := by
  have hE := energy_weight_le q B hB
  have he := error_weight k
  simp only [bounded, rawWeight_sub, rawWeight_scale, rawWeight_square, rawWeight_atom, rawWeight_relabel]
  change 256 + 256 * rawWeight (energy q) + 400 * rawWeight (error k) ≤ _
  omega

theorem allReal_weight_le (q : Fin n → Poly V) (B : ℕ) (hB : ∀ j, rawWeight (q j) ≤ B) (k : ℕ) :
    rawWeight (allReal q k) ≤ 512 + 256 * (n * B ^ 2) + 409600 * (k + 1) := by
  have hE := energy_weight_le q B hB
  have he := error_weight k
  simp only [allReal, rawWeight_sub, rawWeight_scale, rawWeight_product, rawWeight_square,
    rawWeight_atom, rawWeight_constant, rawWeight_relabel]
  change 512 + 256 * rawWeight (energy q) + 400 * rawWeight (error k) ≤ _
  omega

end JointThermoComplexity.Complexity.SparseStrictPolynomial

namespace JointThermoComplexity.Complexity.NumericStrictRawBounds
open RealSyntax SparseInteger SourcePolynomialSchedules NumericStrictData SparseRawPipelineBounds

def termCountBound (L : ℕ) : ℕ := 2 + 9 * (9 * L + 2 * scaleLength L + 3) + 4 * (thresholdLength L + 1)

def coefficientNormBound (s : Sentence) : ℕ :=
  512 + 256 * (paddedEquationCount s * (50 * 2 ^ s.code.length) ^ 2) + 409600 * (thresholdLength s.code.length + 1)

theorem bounded_term_count (s : Sentence) : (NumericStrictData.bounded s).length ≤ termCountBound s.code.length := by
  have h := SparseStrictPolynomial.bounded_length (energyFamily s) 3 (numeric_energy_length s) (thresholdLength s.code.length)
  norm_num only at h
  have hn := NumericStrictData.equation_count s
  rw [NumericStrictData.bounded, length_relabel]
  exact h.trans (by unfold termCountBound; omega)

theorem allReal_term_count (s : Sentence) : (NumericStrictData.allReal s).length ≤ termCountBound s.code.length := by
  have h := SparseStrictPolynomial.allReal_length (energyFamily s) 3 (numeric_energy_length s) (thresholdLength s.code.length)
  norm_num only at h
  have hn := NumericStrictData.equation_count s
  rw [NumericStrictData.allReal, length_relabel]
  exact h.trans (by unfold termCountBound; omega)

theorem bounded_raw_weight (s : Sentence) : rawWeight (NumericStrictData.bounded s) ≤ coefficientNormBound s := by
  have h := SparseStrictPolynomial.bounded_weight_le (energyFamily s) (50 * 2 ^ s.code.length)
    (numeric_energy_weight s) (thresholdLength s.code.length)
  rw [NumericStrictData.bounded, rawWeight_relabel]
  exact h.trans (by unfold coefficientNormBound; omega)

theorem allReal_raw_weight (s : Sentence) : rawWeight (NumericStrictData.allReal s) ≤ coefficientNormBound s := by
  have h := SparseStrictPolynomial.allReal_weight_le (energyFamily s) (50 * 2 ^ s.code.length)
    (numeric_energy_weight s) (thresholdLength s.code.length)
  rw [NumericStrictData.allReal, rawWeight_relabel]
  exact h

theorem bounded_coefficient (s : Sentence) (a : ℤ × List (Fin (variableCount s)))
    (ha : a ∈ NumericStrictData.bounded s) : a.1.natAbs ≤ coefficientNormBound s :=
  (rawWeight_member _ _ ha).trans (bounded_raw_weight s)

theorem allReal_coefficient (s : Sentence) (a : ℤ × List (Fin (variableCount s)))
    (ha : a ∈ NumericStrictData.allReal s) : a.1.natAbs ≤ coefficientNormBound s :=
  (rawWeight_member _ _ ha).trans (allReal_raw_weight s)

end JointThermoComplexity.Complexity.NumericStrictRawBounds

#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.bounded_weight_le
#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.allReal_weight_le
#print axioms JointThermoComplexity.Complexity.NumericStrictRawBounds.bounded_term_count
#print axioms JointThermoComplexity.Complexity.NumericStrictRawBounds.allReal_term_count
#print axioms JointThermoComplexity.Complexity.NumericStrictRawBounds.bounded_coefficient
#print axioms JointThermoComplexity.Complexity.NumericStrictRawBounds.allReal_coefficient
