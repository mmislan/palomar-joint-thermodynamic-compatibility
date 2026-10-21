module
public import proofs.JointThermoComplexity.Complexity.RationalPowerCode
public import proofs.JointThermoComplexity.Complexity.SparseSubstitutionBounds

set_option autoImplicit false
@[expose] public section

/-! Every actual degree-four template supplies the static power-machine weight budget. -/

namespace JointThermoComplexity.Complexity.DenseTemplateDegree
open SparseInteger SparseSubstitution RawNormalizationTemplates
variable {m : ℕ}

theorem cube_degree (hm : m ≤ 4) (a : ℤ × List (Fin m)) (ha : a ∈ cubeTemplate 4 m) : a.2.length ≤ 4 := by
  have hd := degree_scale (1 * (2 : ℤ) ^ (4 - m))
    (degree_expand cubeVariable cubeVariable_degree (List.finRange m))
  have hh : DegreeLE m (cubeTemplate 4 m) := by
    simpa only [cubeTemplate, cubeTerm, List.length_finRange] using hd
  exact (hh a ha).trans hm

theorem orthant_degree (hm : m ≤ 4) (a : ℤ × List (Fin m ⊕ Fin m)) (ha : a ∈ orthantTemplate m) : a.2.length ≤ 4 := by
  have hd := degree_expand orthantVariable orthantVariable_degree (List.finRange m)
  have hh : DegreeLE m (orthantTemplate m) := by
    simpa only [orthantTemplate, List.length_finRange] using hd
  exact (hh a ha).trans hm

theorem cube_weight (hm : m ≤ 4) (a : ℤ × List (Fin m)) (ha : a ∈ cubeTemplate 4 m) :
    PowerCellWord.weight (PowerCellEmit.items (DensePowerPorts.cellLayout m hm).comparisons
      (OccurrencePowerWeights.weight a.2)) ≤ 4 := by
  rw [OccurrencePowerWeights.weight_total]
  exact cube_degree hm a ha

theorem positive_weight (hm : m ≤ 4) (a : ℤ × List (Fin m ⊕ Fin m)) (ha : a ∈ orthantTemplate m) :
    PowerCellWord.weight (PowerCellEmit.items (DensePowerPorts.cellLayout m hm).comparisons
      (OccurrencePowerWeights.weight (DenseTemplatePowerCode.positive a.2))) ≤ 4 := by
  rw [OccurrencePowerWeights.weight_total]
  exact (DenseTemplatePowerCode.positive_length a.2).trans (orthant_degree hm a ha)

theorem negative_weight (hm : m ≤ 4) (a : ℤ × List (Fin m ⊕ Fin m)) (ha : a ∈ orthantTemplate m) :
    PowerCellWord.weight (PowerCellEmit.items (DensePowerPorts.cellLayout m hm).comparisons
      (OccurrencePowerWeights.weight (DenseTemplatePowerCode.negative a.2))) ≤ 4 := by
  rw [OccurrencePowerWeights.weight_total]
  exact (DenseTemplatePowerCode.negative_length a.2).trans (orthant_degree hm a ha)

end JointThermoComplexity.Complexity.DenseTemplateDegree

#print axioms JointThermoComplexity.Complexity.DenseTemplateDegree.cube_weight
#print axioms JointThermoComplexity.Complexity.DenseTemplateDegree.positive_weight
#print axioms JointThermoComplexity.Complexity.DenseTemplateDegree.negative_weight
