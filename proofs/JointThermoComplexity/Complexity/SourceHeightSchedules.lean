module
public import proofs.JointThermoComplexity.Complexity.SourceScaledPadding
public import proofs.JointThermoComplexity.Complexity.QuarterScaleSchedule

set_option autoImplicit false
@[expose] public section

/-! # Explicit polynomial source-chain and strict-threshold schedules

Both schedules use only the original sentence bit length. The witness and
minimum heights occur only in proofs of their adequacy, not in their values.
-/

namespace JointThermoComplexity.Complexity.SourceHeightSchedules
open RealSyntax QuadraticCircuit SourceScaledPadding SourceIntegerWeight SourceSeparation
open DInstabilityComplexity.Separation NaturalHeightBounds QuarterScaleSchedule FixedQuarterSquaring

def sourceChainLength (L : ℕ) : ℕ := heightExponent (5 * L) (3 * L + 11) + 1

def thresholdChainLength (L m : ℕ) : ℕ :=
  heightExponent (10 * L + 2 * m + 2) (11 * L + 2 * m + 19) + 1

def chosenThresholdLength (L : ℕ) : ℕ := thresholdChainLength L (sourceChainLength L)

theorem exponent_monotone {n N b B : ℕ} (hn : n ≤ N) (hb : b ≤ B) :
    heightExponent n b ≤ heightExponent N B :=
  Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 6 hn)
    (Nat.mul_le_mul hb (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hn) 5))) 2

theorem original_squared_length (s : Sentence) :
    quadraticSquaredLength (original s) ≤ (4 * s.code.length + 1) * (3 + 2 ^ s.code.length) ^ 2 := by
  classical
  have hW (j : OriginalIndices s) : weight (original s j) ≤ 3 + 2 ^ s.code.length :=
    (sourceEquations_weight s _ (List.getElem_mem j.isLt)).trans
      (Nat.add_le_add_left s.literalHeight_le_pow_code_length 3)
  unfold quadraticSquaredLength
  calc
    _ ≤ ∑ _j : OriginalIndices s, (3 + 2 ^ s.code.length) ^ 2 :=
      Finset.sum_le_sum (fun j _ => Nat.pow_le_pow_left (hW j) 2)
    _ = (sourceEquations s).length * (3 + 2 ^ s.code.length) ^ 2 := by simp [OriginalIndices]
    _ ≤ _ := Nat.mul_le_mul_right _ (sourceEquations_length_le_code_length s)

theorem original_critical_power (s : Sentence) :
    quadraticCriticalLength (original s) ≤ 2 ^ (3 * s.code.length + 11) := by
  let L := s.code.length
  have hM : 4 * L + 1 ≤ 2 ^ (L + 3) := by
    calc
      4 * L + 1 ≤ 4 * (L + 1) := by omega
      _ ≤ 4 * 2 ^ (L + 1) := Nat.mul_le_mul_left 4 (Nat.lt_two_pow_self : L + 1 < 2 ^ (L + 1)).le
      _ = 2 ^ (L + 3) := by rw [show L + 3 = (L + 1) + 2 by omega, pow_add]; ring
  have hW : 3 + 2 ^ L ≤ 2 ^ (L + 2) := by
    have hp : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have he : 2 ^ (L + 2) = 4 * 2 ^ L := by rw [pow_add]; ring
    rw [he]
    omega
  have h := critical_length_power_bound (quadraticSquaredLength (original s))
    (4 * L + 1) (3 + 2 ^ L) (L + 3) (L + 2) (original_squared_length s) hM hW
  have he : (L + 3) + 2 * (L + 2) + 4 = 3 * L + 11 := by omega
  rw [he] at h
  exact h

theorem sourceHeight_le_cap (s : Sentence) :
    sourceHeight s ≤ heightCap (sourceArity s) (quadraticCriticalLength (original s)) := by
  have hC : 1 ≤ quadraticCriticalLength (original s) := by unfold quadraticCriticalLength; omega
  exact witness_form_le_cap (sourceArity s) (quadraticCriticalLength (original s)) hC

theorem source_scale_bound (s : Sentence) :
    exactChain (sourceChainLength s.code.length) * ((sourceHeight s : ℝ) + 1) ≤ 1 / 4 :=
  quarter_scale_from_cap (sourceArity s) (quadraticCriticalLength (original s)) (3 * s.code.length + 11)
    (sourceHeight s) (sourceChainLength s.code.length) (original_critical_power s) (sourceHeight_le_cap s)
    (Nat.add_le_add_right (exponent_monotone (sourceArity_le_code_length s) le_rfl) 1)

theorem source_iff_chosen_padded_root (s : Sentence) :
    s.Satisfiable ↔ ∃ v, ∀ j,
      (padded s (sourceChainLength s.code.length) j).eval₂ (Int.castRingHom ℝ) v = 0 :=
  source_iff_padded_root s (sourceChainLength s.code.length) (source_scale_bound s)

theorem padded_critical_power (s : Sentence) (m : ℕ) :
    quadraticCriticalLength (padded s m) ≤ 2 ^ (11 * s.code.length + 2 * m + 19) := by
  let L := s.code.length
  have hM : 9 * L + 2 * m + 3 ≤ 2 ^ (9 * L + 2 * m + 3) := (Nat.lt_two_pow_self).le
  have hW : 50 * 2 ^ L ≤ 2 ^ (L + 6) := by
    calc
      _ ≤ 64 * 2 ^ L := Nat.mul_le_mul_right _ (by decide : 50 ≤ 64)
      _ = 2 ^ (L + 6) := by rw [pow_add]; ring
  have h := critical_length_power_bound (quadraticSquaredLength (padded s m))
    (9 * L + 2 * m + 3) (50 * 2 ^ L) (9 * L + 2 * m + 3) (L + 6)
    (padded_squared_length s m) hM hW
  have he : (9 * L + 2 * m + 3) + 2 * (L + 6) + 4 = 11 * L + 2 * m + 19 := by omega
  rw [he] at h
  exact h

theorem padded_minimumHeight_le_cap (s : Sentence) (m : ℕ) :
    minimumHeight (padded s m) ≤ heightCap (Fintype.card (PaddedCoordinates s m))
      (quadraticCriticalLength (padded s m)) := by
  have hGC : quadraticSquaredLength (padded s m) + 1 ≤ quadraticCriticalLength (padded s m) := by
    unfold quadraticCriticalLength
    omega
  exact minimum_form_le_cap _ _ _ hGC

theorem threshold_lt_padded_gap (s : Sentence) (m : ℕ) :
    (1 / 2 : ℝ) ^ (2 ^ thresholdChainLength s.code.length m) <
      1 / ((minimumHeight (padded s m) : ℝ) + 1) :=
  strict_threshold_from_cap (Fintype.card (PaddedCoordinates s m)) (quadraticCriticalLength (padded s m))
    (11 * s.code.length + 2 * m + 19) (minimumHeight (padded s m)) (thresholdChainLength s.code.length m)
    (padded_critical_power s m) (padded_minimumHeight_le_cap s m)
    (Nat.add_le_add_right (exponent_monotone (padded_coordinate_count s m) le_rfl) 1)

theorem source_NO_energy_above_threshold (s : Sentence) (m : ℕ) (hno : ¬s.Satisfiable) :
    ∀ v, (1 / 2 : ℝ) ^ (2 ^ thresholdChainLength s.code.length m) < quadraticEnergy (padded s m) v :=
  fun v => (threshold_lt_padded_gap s m).trans (source_NO_uniform_gap s m hno v)

theorem sourceChainLength_formula (L : ℕ) : sourceChainLength L = 60 * L ^ 2 + 265 * L + 58 := by
  unfold sourceChainLength heightExponent
  ring

theorem thresholdChainLength_formula (L m : ℕ) :
    thresholdChainLength L m = 440 * L ^ 2 + 168 * L * m + 16 * m ^ 2 + 963 * L + 190 * m + 262 := by
  unfold thresholdChainLength heightExponent
  ring

theorem chosenThresholdLength_formula (L : ℕ) :
    chosenThresholdLength L = 57600 * L ^ 4 + 518880 * L ^ 3 + 1291320 * L ^ 2 + 552897 * L + 65106 := by
  rw [chosenThresholdLength, thresholdChainLength_formula, sourceChainLength_formula]
  ring

end JointThermoComplexity.Complexity.SourceHeightSchedules

#print axioms JointThermoComplexity.Complexity.SourceHeightSchedules.source_scale_bound
#print axioms JointThermoComplexity.Complexity.SourceHeightSchedules.source_iff_chosen_padded_root
#print axioms JointThermoComplexity.Complexity.SourceHeightSchedules.threshold_lt_padded_gap
#print axioms JointThermoComplexity.Complexity.SourceHeightSchedules.chosenThresholdLength_formula
