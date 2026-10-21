module
public import proofs.JointThermoComplexity.Complexity.ScaledQuadraticSystem
public import proofs.JointThermoComplexity.Complexity.SourceBoundedQuadratic
public import proofs.JointThermoComplexity.Complexity.SourceCirclePadding

set_option autoImplicit false
@[expose] public section

/-! # Independent source sentences, a forced positive scale and coercive padding

The YES direction has an explicit numerical small-scale condition. The NO
direction and its global minimum gap hold for every chain length. Choosing a
polynomial chain length and proving the binary implementation remain open.
-/

namespace JointThermoComplexity.Complexity.SourceScaledPadding
open RealSyntax QuadraticCircuit FixedQuarterSquaring SourceSeparation SourceIntegerWeight
open DInstabilityComplexity.Separation MvPolynomial QuadraticHomogenization

abbrev OriginalIndices (s : Sentence) := Fin (sourceEquations s).length
abbrev Coordinates (s : Sentence) (m : ℕ) := Fin (sourceArity s) ⊕ Fin (m + 1)
abbrev ScaledIndices (s : Sentence) (m : ℕ) := OriginalIndices s ⊕ (Unit ⊕ Fin m)
abbrev PaddedCoordinates (s : Sentence) (m : ℕ) := Coordinates s m × Bool
abbrev PaddedIndices (s : Sentence) (m : ℕ) := ScaledIndices s m ⊕ Coordinates s m

noncomputable def original (s : Sentence) : OriginalIndices s → MvPolynomial (Fin (sourceArity s)) ℤ :=
  QuadraticWitnessBridge.family (sourceEquations s)

noncomputable def scaled (s : Sentence) (m : ℕ) : ScaledIndices s m → MvPolynomial (Coordinates s m) ℤ :=
  ScaledQuadraticSystem.family (original s) m

noncomputable def padded (s : Sentence) (m : ℕ) : PaddedIndices s m → MvPolynomial (PaddedCoordinates s m) ℤ :=
  circlePadding (scaled s m)

theorem original_degree (s : Sentence) (j : OriginalIndices s) : (original s j).totalDegree ≤ 2 :=
  sourceEquations_quadratic s _ (List.getElem_mem j.isLt)

theorem original_holds_iff (s : Sentence) (x : Fin (sourceArity s) → ℝ) :
    EquationsHold (sourceEquations s) x ↔ ∀ j, (original s j).eval₂ (Int.castRingHom ℝ) x = 0 :=
  QuadraticWitnessBridge.holds_iff_family (sourceEquations s) x

theorem scaled_root_implies_source (s : Sentence) (m : ℕ) (v : Coordinates s m → ℝ)
    (hv : ∀ j, (scaled s m j).eval₂ (Int.castRingHom ℝ) v = 0) : s.Satisfiable := by
  have hx := ScaledQuadraticSystem.root_recovery (original s) (original_degree s) m v hv
  exact (sourceEquations_satisfiable_iff s).mp ⟨_, (original_holds_iff s _).mpr hx⟩

theorem padded_root_implies_source (s : Sentence) (m : ℕ)
    (hp : ∃ v, ∀ j, (padded s m j).eval₂ (Int.castRingHom ℝ) v = 0) : s.Satisfiable := by
  obtain ⟨v, _, hv⟩ := (circlePadding_root_iff (scaled s m)).mp hp
  exact scaled_root_implies_source s m v hv

theorem source_iff_padded_root (s : Sentence) (m : ℕ)
    (hsmall : exactChain m * ((sourceHeight s : ℝ) + 1) ≤ 1 / 4) :
    s.Satisfiable ↔ ∃ v, ∀ j, (padded s m j).eval₂ (Int.castRingHom ℝ) v = 0 := by
  constructor
  · intro hs
    obtain ⟨x, hx, hb⟩ := (source_satisfiable_iff_effectively_bounded s).mp hs
    have hroot := ScaledQuadraticSystem.exactAssignment_root (original s) (original_degree s) m x
      ((original_holds_iff s x).mp hx)
    have hscaled : ∀ i, |exactChain m * x i| ≤ 1 / 4 := by
      intro i
      have hi : |exactChain m * x i| < exactChain m * ((sourceHeight s : ℝ) + 1) := by
        simpa only [abs_mul, abs_of_pos (exactChain_pos m)] using
          mul_lt_mul_of_pos_left (hb i) (exactChain_pos m)
      exact (hi.trans_le hsmall).le
    exact (circlePadding_root_iff (scaled s m)).mpr
      ⟨ScaledQuadraticSystem.exactAssignment m x,
        ScaledQuadraticSystem.exactAssignment_quarter m x hscaled, hroot⟩
  · exact padded_root_implies_source s m

theorem scaled_degree (s : Sentence) (m : ℕ) (j : ScaledIndices s m) :
    (scaled s m j).totalDegree ≤ 2 := ScaledQuadraticSystem.family_degree (original s) m j

theorem padded_degree (s : Sentence) (m : ℕ) (j : PaddedIndices s m) :
    (padded s m j).totalDegree ≤ 2 := circlePadding_quadratic (scaled s m) (scaled_degree s m) j

theorem padded_zero_quarter (s : Sentence) (m : ℕ) (v : PaddedCoordinates s m → ℝ)
    (hv : ∀ j, (padded s m j).eval₂ (Int.castRingHom ℝ) v = 0) :
    ∀ i, |v i| ≤ 1 / 4 := circlePadding_zero_bounds (scaled s m) v hv

theorem padded_zero_half_interior (s : Sentence) (m : ℕ) (v : PaddedCoordinates s m → ℝ)
    (hv : ∀ j, (padded s m j).eval₂ (Int.castRingHom ℝ) v = 0) :
    ∀ i, -(1 / 2 : ℝ) < v i ∧ v i < 1 / 2 := by
  intro i
  apply abs_lt.mp
  exact (padded_zero_quarter s m v hv i).trans_lt (by norm_num : (1 / 4 : ℝ) < 1 / 2)

theorem source_NO_uniform_gap (s : Sentence) (m : ℕ) (hno : ¬s.Satisfiable) :
    ∀ v, 1 / ((minimumHeight (padded s m) : ℝ) + 1) < quadraticEnergy (padded s m) v := by
  apply circlePadding_energy_gap (scaled s m) (scaled_degree s m)
  rintro ⟨v, _, hv⟩
  exact hno (scaled_root_implies_source s m v hv)

theorem padded_coordinate_count (s : Sentence) (m : ℕ) :
    Fintype.card (PaddedCoordinates s m) ≤ 10 * s.code.length + 2 * m + 2 := by
  have hn := sourceArity_le_code_length s
  have hb : Fintype.card Bool = 2 := by decide
  change Fintype.card ((Fin (sourceArity s) ⊕ Fin (m + 1)) × Bool) ≤ _
  rw [Fintype.card_prod, hb, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

theorem padded_equation_count (s : Sentence) (m : ℕ) :
    Fintype.card (PaddedIndices s m) ≤ 9 * s.code.length + 2 * m + 3 := by
  have hn := sourceArity_le_code_length s
  have he := sourceEquations_length_le_code_length s
  change Fintype.card ((Fin (sourceEquations s).length ⊕ (Unit ⊕ Fin m)) ⊕
    (Fin (sourceArity s) ⊕ Fin (m + 1))) ≤ _
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  omega

theorem quarter_circle_weight {V : Type} (i : V) : weight (quarterCirclePolynomial i) ≤ 33 := by
  have hs0 : weight ((X (i, false) : MvPolynomial (V × Bool) ℤ) ^ 2) ≤ 1 := by
    simpa only [pow_two, weight_X] using weight_mul_X (X (i, false) : MvPolynomial (V × Bool) ℤ) (i, false)
  have hs1 : weight ((X (i, true) : MvPolynomial (V × Bool) ℤ) ^ 2) ≤ 1 := by
    simpa only [pow_two, weight_X] using weight_mul_X (X (i, true) : MvPolynomial (V × Bool) ℤ) (i, true)
  have hadd := weight_add ((X (i, false) : MvPolynomial (V × Bool) ℤ) ^ 2) (X (i, true) ^ 2)
  have hmul := weight_mul (C 16 : MvPolynomial (V × Bool) ℤ) (X (i, false) ^ 2 + X (i, true) ^ 2)
  have hsub := weight_sub (C 16 * (X (i, false) ^ 2 + X (i, true) ^ 2) : MvPolynomial (V × Bool) ℤ) 1
  simp only [weight_C, weight_one] at hmul hsub
  change weight (C 16 * (X (i, false) ^ 2 + X (i, true) ^ 2) : MvPolynomial (V × Bool) ℤ) ≤
    16 * weight (X (i, false) ^ 2 + X (i, true) ^ 2) at hmul
  unfold quarterCirclePolynomial
  omega

theorem padded_weight (s : Sentence) (m : ℕ) (j : PaddedIndices s m) :
    weight (padded s m j) ≤ 50 * 2 ^ s.code.length := by
  have hpow : 1 ≤ 2 ^ s.code.length := Nat.one_le_pow _ _ (by decide)
  have hW (i : OriginalIndices s) : weight (original s i) ≤ 3 + 2 ^ s.code.length := by
    have h := sourceEquations_weight s _ (List.getElem_mem i.isLt)
    exact h.trans (Nat.add_le_add_left s.literalHeight_le_pow_code_length 3)
  cases j with
  | inl j =>
    have hs := ScaledQuadraticSystem.family_weight (original s) _ hW m j
    have hr := weight_rename (fun i => (i, false)) (scaled s m j)
    change weight (rename (fun i => (i, false)) (scaled s m j)) ≤ _
    change weight (scaled s m j) ≤ 3 * (3 + 2 ^ s.code.length) + 5 at hs
    omega
  | inr i =>
    change weight (quarterCirclePolynomial i) ≤ _
    exact (quarter_circle_weight i).trans (by omega)

theorem padded_squared_length (s : Sentence) (m : ℕ) :
    quadraticSquaredLength (padded s m) ≤
      (9 * s.code.length + 2 * m + 3) * (50 * 2 ^ s.code.length) ^ 2 := by
  classical
  unfold quadraticSquaredLength
  calc
    _ ≤ ∑ _j : PaddedIndices s m, (50 * 2 ^ s.code.length) ^ 2 :=
      Finset.sum_le_sum (fun j _ => Nat.pow_le_pow_left (padded_weight s m j) 2)
    _ = Fintype.card (PaddedIndices s m) * (50 * 2 ^ s.code.length) ^ 2 := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (padded_equation_count s m)

theorem padded_critical_length (s : Sentence) (m : ℕ) :
    quadraticCriticalLength (padded s m) ≤
      6 + 4 * ((9 * s.code.length + 2 * m + 3) * (50 * 2 ^ s.code.length) ^ 2) :=
  Nat.add_le_add_left (Nat.mul_le_mul_left 4 (padded_squared_length s m)) 6

end JointThermoComplexity.Complexity.SourceScaledPadding

#print axioms JointThermoComplexity.Complexity.SourceScaledPadding.source_iff_padded_root
#print axioms JointThermoComplexity.Complexity.SourceScaledPadding.source_NO_uniform_gap
#print axioms JointThermoComplexity.Complexity.SourceScaledPadding.padded_coordinate_count
#print axioms JointThermoComplexity.Complexity.SourceScaledPadding.padded_weight
#print axioms JointThermoComplexity.Complexity.SourceScaledPadding.padded_critical_length
