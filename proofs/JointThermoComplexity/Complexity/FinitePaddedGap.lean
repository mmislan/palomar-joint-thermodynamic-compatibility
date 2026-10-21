module
public import proofs.JointThermoComplexity.Complexity.FinitePaddedSemantics

set_option autoImplicit false
@[expose] public section

/-! A global NO energy gap for the generic parsed system and its explicit
polynomial threshold schedule. Heights occur only in proofs, not in data.
-/

namespace JointThermoComplexity.Complexity.FinitePaddedGap
open EquationSystemCodec FiniteStrictData FinitePaddedSemantics SourceIntegerWeight SourceSeparation
open NaturalHeightBounds QuarterScaleSchedule SourceHeightSchedules DInstabilityComplexity.Separation

theorem uniform_gap (p : Data) (hp : FiniteEquationHardness.Domain p)
    (hn : ¬ FiniteEquationSemantics.Feasible p.rows) :
    ∀ v, 1 / ((minimumHeight (paddedSystem p) : ℝ) + 1) < quadraticEnergy (paddedSystem p) v := by
  apply circlePadding_energy_gap (scaledSystem p) (scaled_degree p)
  rintro ⟨v, _, hv⟩
  exact hn ((FiniteSystemHeight.feasible_iff_root p).mpr
    ((ScaledQuadraticSystem.common_root_iff (FiniteSystemHeight.system p) (FiniteSystemHeight.system_degree p hp)
      (scaleCount p)).mp ⟨v, hv⟩))

theorem coordinate_count (p : Data) : Fintype.card (PaddedCoordinates p) ≤ 10 * inputLength p + 2 * scaleCount p + 2 := by
  have he := Fintype.card_congr (paddedCoordinateEnumeration p)
  simp only [Fintype.card_fin] at he
  rw [he]
  have hn : p.arity ≤ inputLength p := EquationCodeBounds.arity_le_length p
  dsimp [scaleCoordinateCount]
  omega

theorem equation_count (p : Data) : Fintype.card (PaddedIndices p) ≤ 9 * inputLength p + 2 * scaleCount p + 3 := by
  have he := Fintype.card_congr (paddedIndexEnumeration p)
  simp only [Fintype.card_fin] at he
  rw [he]
  have hn := FiniteStrictBounds.padded_count p
  omega

theorem padded_weight (p : Data) (hp : FiniteEquationHardness.Domain p) (j : PaddedIndices p) :
    weight (paddedSystem p j) ≤ 50 * 2 ^ inputLength p := by
  rw [← interpret_padded]
  have h := (FiniteSystemHeight.interpret_weight_le (paddedFamily p j)).trans
    (FiniteStrictBounds.padded_weight p hp j)
  have hpow : 1 ≤ 2 ^ inputLength p := Nat.one_le_two_pow
  omega

theorem squared_length (p : Data) (hp : FiniteEquationHardness.Domain p) :
    quadraticSquaredLength (paddedSystem p) ≤
      (9 * inputLength p + 2 * scaleCount p + 3) * (50 * 2 ^ inputLength p) ^ 2 := by
  classical
  unfold quadraticSquaredLength
  calc
    _ ≤ ∑ _j : PaddedIndices p, (50 * 2 ^ inputLength p) ^ 2 :=
      Finset.sum_le_sum (fun j _ => Nat.pow_le_pow_left (padded_weight p hp j) 2)
    _ = Fintype.card (PaddedIndices p) * (50 * 2 ^ inputLength p) ^ 2 := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (equation_count p)

theorem critical_power (p : Data) (hp : FiniteEquationHardness.Domain p) :
    quadraticCriticalLength (paddedSystem p) ≤ 2 ^ (11 * inputLength p + 2 * scaleCount p + 19) := by
  let L := inputLength p
  let m := scaleCount p
  have hM : 9 * L + 2 * m + 3 ≤ 2 ^ (9 * L + 2 * m + 3) := (Nat.lt_two_pow_self).le
  have hW : 50 * 2 ^ L ≤ 2 ^ (L + 6) := by
    calc
      _ ≤ 64 * 2 ^ L := Nat.mul_le_mul_right _ (by decide : 50 ≤ 64)
      _ = _ := by rw [pow_add]; ring
  have h := critical_length_power_bound (quadraticSquaredLength (paddedSystem p))
    (9 * L + 2 * m + 3) (50 * 2 ^ L) (9 * L + 2 * m + 3) (L + 6) (squared_length p hp) hM hW
  have he : (9 * L + 2 * m + 3) + 2 * (L + 6) + 4 = 11 * L + 2 * m + 19 := by omega
  rw [he] at h
  exact h

theorem minimumHeight_le_cap (p : Data) :
    minimumHeight (paddedSystem p) ≤ heightCap (Fintype.card (PaddedCoordinates p))
      (quadraticCriticalLength (paddedSystem p)) := by
  have hGC : quadraticSquaredLength (paddedSystem p) + 1 ≤ quadraticCriticalLength (paddedSystem p) := by
    unfold quadraticCriticalLength
    omega
  exact minimum_form_le_cap _ _ _ hGC

theorem threshold_schedule_eq (p : Data) :
    thresholdCount p = thresholdChainLength (inputLength p) (scaleCount p) := by
  change SourcePolynomialSchedules.thresholdLength (inputLength p) =
    thresholdChainLength (inputLength p) (SourcePolynomialSchedules.scaleLength (inputLength p))
  rw [show SourcePolynomialSchedules.scaleLength (inputLength p) = sourceChainLength (inputLength p) from
    (sourceChainLength_formula (inputLength p)).symm]
  exact (chosenThresholdLength_formula (inputLength p)).symm

theorem threshold_lt_gap (p : Data) (hp : FiniteEquationHardness.Domain p) :
    (1 / 2 : ℝ) ^ (2 ^ thresholdCount p) < 1 / ((minimumHeight (paddedSystem p) : ℝ) + 1) := by
  rw [threshold_schedule_eq]
  exact strict_threshold_from_cap (Fintype.card (PaddedCoordinates p)) (quadraticCriticalLength (paddedSystem p))
    (11 * inputLength p + 2 * scaleCount p + 19) (minimumHeight (paddedSystem p))
    (thresholdChainLength (inputLength p) (scaleCount p)) (critical_power p hp) (minimumHeight_le_cap p)
    (Nat.add_le_add_right (exponent_monotone (coordinate_count p) le_rfl) 1)

theorem NO_energy_above_threshold (p : Data) (hp : FiniteEquationHardness.Domain p)
    (hn : ¬ FiniteEquationSemantics.Feasible p.rows) :
    ∀ v, (1 / 2 : ℝ) ^ (2 ^ thresholdCount p) < quadraticEnergy (paddedSystem p) v :=
  fun v => (threshold_lt_gap p hp).trans (uniform_gap p hp hn v)

end JointThermoComplexity.Complexity.FinitePaddedGap

#print axioms JointThermoComplexity.Complexity.FinitePaddedGap.uniform_gap
#print axioms JointThermoComplexity.Complexity.FinitePaddedGap.threshold_schedule_eq
#print axioms JointThermoComplexity.Complexity.FinitePaddedGap.NO_energy_above_threshold
