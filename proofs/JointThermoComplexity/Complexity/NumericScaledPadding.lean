module
public import proofs.JointThermoComplexity.Complexity.NumericSourceHeight
public import proofs.JointThermoComplexity.Complexity.SparseCircleSemantics

set_option autoImplicit false
@[expose] public section

/-! # Quantitative scale/circle composition for the executable numbered source

The padded sparse data is fixed by the source and chain length. Its common
witness and global NO gap are derived from the checked effective mathematics.
-/

namespace JointThermoComplexity.Complexity.NumericScaledPadding
open RealSyntax SourceCoordinateEnumeration SourceIntegerWeight SourceSeparation
open SourceHeightSchedules NaturalHeightBounds QuarterScaleSchedule FixedQuarterSquaring
open DInstabilityComplexity.Separation

abbrev Coordinates (s : Sentence) (m : ℕ) := SparseScaledSource.Coordinates s m
abbrev ScaledIndices (s : Sentence) (m : ℕ) := SparseScaledSource.Indices s m
abbrev PaddedCoordinates (s : Sentence) (m : ℕ) := Coordinates s m × Bool
abbrev PaddedIndices (s : Sentence) (m : ℕ) := ScaledIndices s m ⊕ Coordinates s m

def padded (s : Sentence) (m : ℕ) : PaddedIndices s m → SparseInteger.Poly (PaddedCoordinates s m) :=
  SparseCirclePadding.family (SparseScaledSource.family s m)

noncomputable def scaledSystem (s : Sentence) (m : ℕ) :
    ScaledIndices s m → MvPolynomial (Coordinates s m) ℤ := ScaledQuadraticSystem.family (NumericSourceHeight.system s) m

noncomputable def paddedSystem (s : Sentence) (m : ℕ) :
    PaddedIndices s m → MvPolynomial (PaddedCoordinates s m) ℤ := circlePadding (scaledSystem s m)

theorem interpret_scaled (s : Sentence) (m : ℕ) (j : ScaledIndices s m) :
    SparseInteger.interpret (SparseScaledSource.family s m j) = scaledSystem s m j :=
  SparseScaledSource.interpret_family s m j

theorem interpret_padded (s : Sentence) (m : ℕ) (j : PaddedIndices s m) :
    SparseInteger.interpret (padded s m j) = paddedSystem s m j := by
  simp only [padded, paddedSystem, SparseCirclePadding.interpret_family, interpret_scaled]

theorem raw_degree (s : Sentence) (m : ℕ) (j : PaddedIndices s m) : SparseInteger.DegreeLE 2 (padded s m j) :=
  SparseCirclePadding.family_degree _ (SparseScaledSource.family_raw_degree s m) j

theorem scaled_degree (s : Sentence) (m : ℕ) (j : ScaledIndices s m) : (scaledSystem s m j).totalDegree ≤ 2 :=
  ScaledQuadraticSystem.family_degree (NumericSourceHeight.system s) m j

theorem padded_degree (s : Sentence) (m : ℕ) (j : PaddedIndices s m) : (paddedSystem s m j).totalDegree ≤ 2 :=
  circlePadding_quadratic (scaledSystem s m) (scaled_degree s m) j

theorem padded_root_implies_source (s : Sentence) (m : ℕ)
    (hp : ∃ v, ∀ j, (paddedSystem s m j).eval₂ (Int.castRingHom ℝ) v = 0) : s.Satisfiable := by
  obtain ⟨v, _, hv⟩ := (circlePadding_root_iff (scaledSystem s m)).mp hp
  exact (NumericSourceHeight.source_iff_system_root s).mpr
    ((ScaledQuadraticSystem.common_root_iff (NumericSourceHeight.system s) (NumericSourceHeight.system_degree s) m).mp ⟨v, hv⟩)

theorem source_iff_padded_root (s : Sentence) (m : ℕ)
    (hsmall : exactChain m * ((NumericSourceHeight.height s : ℝ) + 1) ≤ 1 / 4) :
    s.Satisfiable ↔ ∃ v, ∀ j, (paddedSystem s m j).eval₂ (Int.castRingHom ℝ) v = 0 := by
  constructor
  · intro hs
    obtain ⟨x, hx, hb⟩ := NumericSourceHeight.exists_bounded s hs
    have hroot := ScaledQuadraticSystem.exactAssignment_root (NumericSourceHeight.system s)
      (NumericSourceHeight.system_degree s) m x hx
    have hscaled : ∀ i, |exactChain m * x i| ≤ 1 / 4 := by
      intro i
      have hi : |exactChain m * x i| < exactChain m * ((NumericSourceHeight.height s : ℝ) + 1) := by
        simpa only [abs_mul, abs_of_pos (exactChain_pos m)] using mul_lt_mul_of_pos_left (hb i) (exactChain_pos m)
      exact (hi.trans_le hsmall).le
    exact (circlePadding_root_iff (scaledSystem s m)).mpr
      ⟨ScaledQuadraticSystem.exactAssignment m x, ScaledQuadraticSystem.exactAssignment_quarter m x hscaled, hroot⟩
  · exact padded_root_implies_source s m

theorem source_iff_chosen_padded_root (s : Sentence) :
    s.Satisfiable ↔ ∃ v, ∀ j, (paddedSystem s (sourceChainLength s.code.length) j).eval₂ (Int.castRingHom ℝ) v = 0 :=
  source_iff_padded_root s _ (NumericSourceHeight.chosen_scale_bound s)

theorem padded_zero_half_interior (s : Sentence) (m : ℕ) (v : PaddedCoordinates s m → ℝ)
    (hv : ∀ j, (paddedSystem s m j).eval₂ (Int.castRingHom ℝ) v = 0) :
    ∀ i, -(1 / 2 : ℝ) < v i ∧ v i < 1 / 2 := by
  intro i
  apply abs_lt.mp
  exact (circlePadding_zero_bounds (scaledSystem s m) v hv i).trans_lt (by norm_num : (1 / 4 : ℝ) < 1 / 2)

theorem source_NO_uniform_gap (s : Sentence) (m : ℕ) (hn : ¬s.Satisfiable) :
    ∀ v, 1 / ((minimumHeight (paddedSystem s m) : ℝ) + 1) < quadraticEnergy (paddedSystem s m) v := by
  apply circlePadding_energy_gap (scaledSystem s m) (scaled_degree s m)
  rintro ⟨v, _, hv⟩
  exact hn ((NumericSourceHeight.source_iff_system_root s).mpr
    ((ScaledQuadraticSystem.common_root_iff (NumericSourceHeight.system s) (NumericSourceHeight.system_degree s) m).mp ⟨v, hv⟩))

theorem padded_coordinate_count (s : Sentence) (m : ℕ) :
    Fintype.card (PaddedCoordinates s m) ≤ 10 * s.code.length + 2 * m + 2 := by
  have hn := NumericSparseSource.coordinate_count s
  have hb : Fintype.card Bool = 2 := by decide
  change Fintype.card ((Fin (sourceCount s) ⊕ Fin (m + 1)) × Bool) ≤ _
  rw [Fintype.card_prod, hb, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

theorem padded_equation_count (s : Sentence) (m : ℕ) :
    Fintype.card (PaddedIndices s m) ≤ 9 * s.code.length + 2 * m + 3 := by
  have hn := NumericSparseSource.coordinate_count s
  have he := NumericSparseSource.equation_count s
  change Fintype.card ((Fin (NumericSparseSource.equations s).length ⊕ (Unit ⊕ Fin m)) ⊕
    (Fin (sourceCount s) ⊕ Fin (m + 1))) ≤ _
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  omega

theorem padded_weight (s : Sentence) (m : ℕ) (j : PaddedIndices s m) :
    weight (paddedSystem s m j) ≤ 50 * 2 ^ s.code.length := by
  have hpow : 1 ≤ 2 ^ s.code.length := Nat.one_le_two_pow
  cases j with
  | inl j =>
    have hs := ScaledQuadraticSystem.family_weight (NumericSourceHeight.system s) _ (NumericSourceHeight.system_weight s) m j
    have hr := weight_rename (fun i => (i, false)) (scaledSystem s m j)
    change weight (MvPolynomial.rename (fun i => (i, false)) (scaledSystem s m j)) ≤ _
    change weight (scaledSystem s m j) ≤ 3 * (3 + 2 ^ s.code.length) + 5 at hs
    omega
  | inr i =>
    change weight (quarterCirclePolynomial i) ≤ _
    exact (SourceScaledPadding.quarter_circle_weight i).trans (by omega)

theorem padded_squared_length (s : Sentence) (m : ℕ) :
    quadraticSquaredLength (paddedSystem s m) ≤ (9 * s.code.length + 2 * m + 3) * (50 * 2 ^ s.code.length) ^ 2 := by
  classical
  unfold quadraticSquaredLength
  calc
    _ ≤ ∑ _j : PaddedIndices s m, (50 * 2 ^ s.code.length) ^ 2 :=
      Finset.sum_le_sum (fun j _ => Nat.pow_le_pow_left (padded_weight s m j) 2)
    _ = Fintype.card (PaddedIndices s m) * (50 * 2 ^ s.code.length) ^ 2 := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (padded_equation_count s m)

theorem padded_critical_power (s : Sentence) (m : ℕ) :
    quadraticCriticalLength (paddedSystem s m) ≤ 2 ^ (11 * s.code.length + 2 * m + 19) := by
  let L := s.code.length
  have hM : 9 * L + 2 * m + 3 ≤ 2 ^ (9 * L + 2 * m + 3) := (Nat.lt_two_pow_self).le
  have hW : 50 * 2 ^ L ≤ 2 ^ (L + 6) := by
    calc
      _ ≤ 64 * 2 ^ L := Nat.mul_le_mul_right _ (by decide : 50 ≤ 64)
      _ = _ := by rw [pow_add]; ring
  have h := critical_length_power_bound (quadraticSquaredLength (paddedSystem s m))
    (9 * L + 2 * m + 3) (50 * 2 ^ L) (9 * L + 2 * m + 3) (L + 6) (padded_squared_length s m) hM hW
  have he : (9 * L + 2 * m + 3) + 2 * (L + 6) + 4 = 11 * L + 2 * m + 19 := by omega
  rw [he] at h
  exact h

theorem padded_minimumHeight_le_cap (s : Sentence) (m : ℕ) :
    minimumHeight (paddedSystem s m) ≤ heightCap (Fintype.card (PaddedCoordinates s m))
      (quadraticCriticalLength (paddedSystem s m)) := by
  have hGC : quadraticSquaredLength (paddedSystem s m) + 1 ≤ quadraticCriticalLength (paddedSystem s m) := by
    unfold quadraticCriticalLength
    omega
  exact minimum_form_le_cap _ _ _ hGC

theorem threshold_lt_padded_gap (s : Sentence) (m : ℕ) :
    (1 / 2 : ℝ) ^ (2 ^ thresholdChainLength s.code.length m) < 1 / ((minimumHeight (paddedSystem s m) : ℝ) + 1) :=
  strict_threshold_from_cap (Fintype.card (PaddedCoordinates s m)) (quadraticCriticalLength (paddedSystem s m))
    (11 * s.code.length + 2 * m + 19) (minimumHeight (paddedSystem s m)) (thresholdChainLength s.code.length m)
    (padded_critical_power s m) (padded_minimumHeight_le_cap s m)
    (Nat.add_le_add_right (exponent_monotone (padded_coordinate_count s m) le_rfl) 1)

theorem source_NO_energy_above_threshold (s : Sentence) (m : ℕ) (hn : ¬s.Satisfiable) :
    ∀ v, (1 / 2 : ℝ) ^ (2 ^ thresholdChainLength s.code.length m) < quadraticEnergy (paddedSystem s m) v :=
  fun v => (threshold_lt_padded_gap s m).trans (source_NO_uniform_gap s m hn v)

end JointThermoComplexity.Complexity.NumericScaledPadding

#print axioms JointThermoComplexity.Complexity.NumericScaledPadding.interpret_padded
#print axioms JointThermoComplexity.Complexity.NumericScaledPadding.source_iff_chosen_padded_root
#print axioms JointThermoComplexity.Complexity.NumericScaledPadding.padded_coordinate_count
#print axioms JointThermoComplexity.Complexity.NumericScaledPadding.padded_weight
#print axioms JointThermoComplexity.Complexity.NumericScaledPadding.source_NO_energy_above_threshold
