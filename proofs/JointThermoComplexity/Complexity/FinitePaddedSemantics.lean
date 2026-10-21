module
public import proofs.JointThermoComplexity.Complexity.FiniteSystemHeight
public import proofs.JointThermoComplexity.Complexity.NumericScaledPadding

set_option autoImplicit false
@[expose] public section

/-! The explicit scale/circle data preserves real common roots and places its
zero witnesses strictly inside the half cube, for the chosen encoded schedule.
-/

namespace JointThermoComplexity.Complexity.FinitePaddedSemantics
open SparseInteger EquationSystemCodec FiniteStrictData FixedQuarterSquaring SourceSeparation
open DInstabilityComplexity.Separation

noncomputable def scaledSystem (p : Data) : ScaleIndices p → MvPolynomial (ScaleCoordinates p) ℤ :=
  ScaledQuadraticSystem.family (FiniteSystemHeight.system p) (scaleCount p)

noncomputable def paddedSystem (p : Data) : PaddedIndices p → MvPolynomial (PaddedCoordinates p) ℤ :=
  circlePadding (scaledSystem p)

theorem interpret_scaled (p : Data) (j : ScaleIndices p) : interpret (scaledFamily p j) = scaledSystem p j :=
  SparseScaledSystem.interpret_family (original p) (scaleCount p) j

theorem interpret_padded (p : Data) (j : PaddedIndices p) : interpret (paddedFamily p j) = paddedSystem p j := by
  simp only [paddedFamily, paddedSystem, SparseCirclePadding.interpret_family, interpret_scaled]

theorem scaled_degree (p : Data) (j : ScaleIndices p) : (scaledSystem p j).totalDegree ≤ 2 :=
  ScaledQuadraticSystem.family_degree (FiniteSystemHeight.system p) (scaleCount p) j

theorem padded_degree (p : Data) (j : PaddedIndices p) : (paddedSystem p j).totalDegree ≤ 2 :=
  circlePadding_quadratic (scaledSystem p) (scaled_degree p) j

theorem padded_root_implies_feasible (p : Data) (hp : FiniteEquationHardness.Domain p)
    (hf : ∃ v, ∀ j, (paddedSystem p j).eval₂ (Int.castRingHom ℝ) v = 0) :
    FiniteEquationSemantics.Feasible p.rows := by
  obtain ⟨v, _, hv⟩ := (circlePadding_root_iff (scaledSystem p)).mp hf
  exact (FiniteSystemHeight.feasible_iff_root p).mpr
    ((ScaledQuadraticSystem.common_root_iff (FiniteSystemHeight.system p) (FiniteSystemHeight.system_degree p hp)
      (scaleCount p)).mp ⟨v, hv⟩)

theorem feasible_iff_padded_root (p : Data) (hp : FiniteEquationHardness.Domain p) :
    FiniteEquationSemantics.Feasible p.rows ↔
      ∃ v, ∀ j, (paddedSystem p j).eval₂ (Int.castRingHom ℝ) v = 0 := by
  constructor
  · intro hf
    obtain ⟨x, hx, hb⟩ := FiniteSystemHeight.exists_bounded p hp hf
    have hroot := ScaledQuadraticSystem.exactAssignment_root (FiniteSystemHeight.system p)
      (FiniteSystemHeight.system_degree p hp) (scaleCount p) x hx
    have hscaled : ∀ i, |exactChain (scaleCount p) * x i| ≤ 1 / 4 := by
      intro i
      have hi : |exactChain (scaleCount p) * x i| <
          exactChain (scaleCount p) * ((FiniteSystemHeight.height p : ℝ) + 1) := by
        simpa only [abs_mul, abs_of_pos (exactChain_pos (scaleCount p))] using
          mul_lt_mul_of_pos_left (hb i) (exactChain_pos (scaleCount p))
      exact (hi.trans_le (FiniteSystemHeight.chosen_scale_bound p hp)).le
    exact (circlePadding_root_iff (scaledSystem p)).mpr
      ⟨ScaledQuadraticSystem.exactAssignment (scaleCount p) x,
        ScaledQuadraticSystem.exactAssignment_quarter (scaleCount p) x hscaled, hroot⟩
  · exact padded_root_implies_feasible p hp

theorem padded_zero_half_interior (p : Data) (v : PaddedCoordinates p → ℝ)
    (hv : ∀ j, (paddedSystem p j).eval₂ (Int.castRingHom ℝ) v = 0) :
    ∀ i, -(1 / 2 : ℝ) < v i ∧ v i < 1 / 2 := by
  intro i
  apply abs_lt.mp
  exact (circlePadding_zero_bounds (scaledSystem p) v hv i).trans_lt (by norm_num : (1 / 4 : ℝ) < 1 / 2)

end JointThermoComplexity.Complexity.FinitePaddedSemantics

#print axioms JointThermoComplexity.Complexity.FinitePaddedSemantics.interpret_padded
#print axioms JointThermoComplexity.Complexity.FinitePaddedSemantics.feasible_iff_padded_root
#print axioms JointThermoComplexity.Complexity.FinitePaddedSemantics.padded_zero_half_interior
