module
public import proofs.JointThermoComplexity.Complexity.StrictRawBounds
public import proofs.JointThermoComplexity.Complexity.NaturalHeightBounds

set_option autoImplicit false
@[expose] public section

/-! # Polynomial bit bounds for every stored strict-source coefficient

The scalar power estimate follows the previously checked canonical-coefficient
argument, applied here to the raw list norm. No cancellation is used.
-/

namespace JointThermoComplexity.Complexity.RawSourceMagnitude
open RealSyntax SourcePolynomialSchedules NumericStrictData NumericStrictRawBounds NaturalHeightBounds

def coefficientBitsBound (L : ℕ) : ℕ := 11 * L + 2 * scaleLength L + thresholdLength L + 29
def coordinateBound (L : ℕ) : ℕ :=
  57600 * L ^ 4 + 518880 * L ^ 3 + 1291440 * L ^ 2 + 553437 * L + 65225

theorem coefficientBitsBound_formula (L : ℕ) :
    coefficientBitsBound L = 57600 * L ^ 4 + 518880 * L ^ 3 + 1291440 * L ^ 2 + 553438 * L + 65251 := by
  unfold coefficientBitsBound scaleLength thresholdLength
  ring

theorem termCountBound_formula (L : ℕ) :
    termCountBound L = 230400 * L ^ 4 + 2075520 * L ^ 3 + 5166360 * L ^ 2 + 2216439 * L + 261501 := by
  unfold termCountBound scaleLength thresholdLength
  ring

theorem coordinate_count (s : Sentence) : variableCount s ≤ coordinateBound s.code.length :=
  NumericStrictData.coordinate_count_polynomial s

theorem scalar_norm_pow {w G L m k : ℕ}
    (hw : w ≤ 512 + 256 * G + 409600 * (k + 1)) (hG : G ≤ 2 ^ (11 * L + 2 * m + 19)) :
    w < 2 ^ (11 * L + 2 * m + k + 29) := by
  let D := 11 * L + 2 * m + k + 27
  have henergy : 256 * G ≤ 2 ^ (11 * L + 2 * m + 27) := by
    calc
      _ ≤ 256 * 2 ^ (11 * L + 2 * m + 19) := Nat.mul_le_mul_left 256 hG
      _ = _ := by rw [show 11 * L + 2 * m + 27 = (11 * L + 2 * m + 19) + 8 by omega, pow_add]; ring
  have herror : 409600 * (k + 1) ≤ 2 ^ (k + 20) := by
    calc
      _ ≤ 2 ^ 19 * 2 ^ (k + 1) := Nat.mul_le_mul (by decide) (Nat.lt_two_pow_self).le
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hpE : 2 ^ (11 * L + 2 * m + 27) ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) (by dsimp [D]; omega)
  have hpe : 2 ^ (k + 20) ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) (by dsimp [D]; omega)
  have hp0 : 512 ≤ 2 ^ D := by
    change 2 ^ 9 ≤ 2 ^ D
    exact Nat.pow_le_pow_right (by decide) (by dsimp [D]; omega)
  have hpos : 0 < 2 ^ D := pow_pos (by decide) _
  calc
    w ≤ 3 * 2 ^ D := by omega
    _ < 4 * 2 ^ D := by omega
    _ = _ := by rw [show 11 * L + 2 * m + k + 29 = D + 2 by dsimp [D], pow_add]; ring

theorem energy_norm_pow (s : Sentence) :
    paddedEquationCount s * (50 * 2 ^ s.code.length) ^ 2 ≤
      2 ^ (11 * s.code.length + 2 * scaleLength s.code.length + 19) := by
  let L := s.code.length
  let m := scaleLength L
  have hn := NumericStrictData.equation_count s
  have hM : 9 * L + 2 * m + 3 ≤ 2 ^ (9 * L + 2 * m + 3) := (Nat.lt_two_pow_self).le
  have hW : 50 * 2 ^ L ≤ 2 ^ (L + 6) := by
    calc
      _ ≤ 64 * 2 ^ L := Nat.mul_le_mul_right _ (by decide : 50 ≤ 64)
      _ = _ := by rw [pow_add]; ring
  have h := critical_length_power_bound (paddedEquationCount s * (50 * 2 ^ L) ^ 2)
    (9 * L + 2 * m + 3) (50 * 2 ^ L) (9 * L + 2 * m + 3) (L + 6)
    (Nat.mul_le_mul_right _ hn) hM hW
  have he : (9 * L + 2 * m + 3) + 2 * (L + 6) + 4 = 11 * L + 2 * m + 19 := by omega
  rw [he] at h
  change paddedEquationCount s * (50 * 2 ^ L) ^ 2 ≤ 2 ^ (11 * L + 2 * m + 19)
  omega

theorem norm_lt_pow (s : Sentence) : coefficientNormBound s < 2 ^ coefficientBitsBound s.code.length :=
  scalar_norm_pow (G := paddedEquationCount s * (50 * 2 ^ s.code.length) ^ 2) le_rfl (energy_norm_pow s)

theorem bounded_coefficient_bits (s : Sentence) (a : ℤ × List (Fin (variableCount s)))
    (ha : a ∈ NumericStrictData.bounded s) : a.1.natAbs.bits.length ≤ coefficientBitsBound s.code.length := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr ((NumericStrictRawBounds.bounded_coefficient s a ha).trans_lt (norm_lt_pow s))

theorem allReal_coefficient_bits (s : Sentence) (a : ℤ × List (Fin (variableCount s)))
    (ha : a ∈ NumericStrictData.allReal s) : a.1.natAbs.bits.length ≤ coefficientBitsBound s.code.length := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr ((NumericStrictRawBounds.allReal_coefficient s a ha).trans_lt (norm_lt_pow s))

theorem bounded_coefficient_code (s : Sentence) (a : ℤ × List (Fin (variableCount s)))
    (ha : a ∈ NumericStrictData.bounded s) : (BitCodec.integerCode a.1).length ≤ 2 * coefficientBitsBound s.code.length + 2 := by
  rw [BitCodec.integerCode_length]
  have h := bounded_coefficient_bits s a ha
  omega

theorem allReal_coefficient_code (s : Sentence) (a : ℤ × List (Fin (variableCount s)))
    (ha : a ∈ NumericStrictData.allReal s) : (BitCodec.integerCode a.1).length ≤ 2 * coefficientBitsBound s.code.length + 2 := by
  rw [BitCodec.integerCode_length]
  have h := allReal_coefficient_bits s a ha
  omega

end JointThermoComplexity.Complexity.RawSourceMagnitude

#print axioms JointThermoComplexity.Complexity.RawSourceMagnitude.energy_norm_pow
#print axioms JointThermoComplexity.Complexity.RawSourceMagnitude.norm_lt_pow
#print axioms JointThermoComplexity.Complexity.RawSourceMagnitude.bounded_coefficient_code
#print axioms JointThermoComplexity.Complexity.RawSourceMagnitude.allReal_coefficient_code
