module
public import proofs.JointThermoComplexity.Complexity.OffsetTemplateProgram
public import proofs.JointThermoComplexity.Complexity.DegreeFourTemplates

set_option autoImplicit false
@[expose] public section

/-! Concrete normalization tables for the offset program. The coefficient
and monomial-length projection preserves exact raw term order and weights. -/

namespace JointThermoComplexity.Complexity.OffsetTemplateData
open SparseInteger SparseSubstitution RawNormalizationTemplates
variable {V W : Type}

def rows (p : Poly V) : List OffsetTemplateProgram.Row := p.map (fun a => (a.1, a.2.length))

def template (boxed : Bool) (m : ℕ) : List OffsetTemplateProgram.Row :=
  if boxed then rows (cubeTemplate 4 m) else rows (orthantTemplate m)

def rawSum (p : Poly V) : ℕ :=
  (p.map (fun a => RationalBranchCoefficients.rightDenominator a.1 * 2 ^ a.2.length)).sum

theorem cube_degree_all (m : ℕ) (hm : m ≤ 4) :
    (cubeTemplate 4 m).all (fun a => decide (a.2.length ≤ 4)) = true := by
  interval_cases m <;> decide

theorem orthant_degree_all (m : ℕ) (hm : m ≤ 4) :
    (orthantTemplate m).all (fun a => decide (a.2.length ≤ 4)) = true := by
  interval_cases m <;> decide

theorem rows_bounded (p : Poly V) (hc : ∀ a ∈ p, a.1.natAbs ≤ 81)
    (hd : ∀ a ∈ p, a.2.length ≤ 4) : OffsetTemplateProgram.Bounded (rows p) := by
  intro row hrow
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hrow
  exact ⟨hc a ha, hd a ha⟩

theorem template_bounded (boxed : Bool) (m : ℕ) (hm : m ≤ 4) :
    OffsetTemplateProgram.Bounded (template boxed m) := by
  cases boxed with
  | false =>
    apply rows_bounded
    · intro a ha
      rw [DegreeFourTemplates.orthant_magnitude m hm a ha]
      decide
    · intro a ha
      exact of_decide_eq_true ((List.all_eq_true.mp (orthant_degree_all m hm)) a ha)
  | true =>
    apply rows_bounded
    · intro a ha
      exact (DegreeFourTemplates.cube_magnitude_bounds m hm a ha).2
    · intro a ha
      exact of_decide_eq_true ((List.all_eq_true.mp (cube_degree_all m hm)) a ha)

theorem template_length (boxed : Bool) (m : ℕ) (hm : m ≤ 4) : (template boxed m).length ≤ 16 := by
  cases boxed with
  | false => simpa only [template, Bool.false_eq_true, ↓reduceIte, rows, List.length_map] using
      DegreeFourTemplates.orthant_length_le m hm
  | true => simpa only [template, ↓reduceIte, rows, List.length_map] using
      DegreeFourTemplates.cube_length_le m hm

theorem total_rows_relabel (c : ℤ) (f : V → W) (p : Poly V) :
    OffsetTemplateProgram.total (decide (c < 0)) c.natAbs (rows p) = rawSum (scale c (relabel f p)) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change OffsetWeightControl.weight (decide (c < 0)) c.natAbs a.1 a.2.length +
        OffsetTemplateProgram.total (decide (c < 0)) c.natAbs (rows p) =
      RationalBranchCoefficients.rightDenominator (c * a.1) * 2 ^ (a.2.map f).length + rawSum (scale c (relabel f p))
    rw [OffsetWeightControl.weight_integer, List.length_map, ih]

theorem cube_total (c : ℤ) (vs : List V) :
    OffsetTemplateProgram.total (decide (c < 0)) c.natAbs (template true vs.length) = rawSum (cubeTerm 4 (c, vs)) := by
  rw [cubeTerm_from_template]
  exact total_rows_relabel c (lookup vs) (cubeTemplate 4 vs.length)

theorem orthant_total (c : ℤ) (vs : List V) :
    OffsetTemplateProgram.total (decide (c < 0)) c.natAbs (template false vs.length) =
      rawSum (scale c (expand orthantVariable vs)) := by
  rw [orthantTerm_from_template]
  exact total_rows_relabel c (Sum.map (lookup vs) (lookup vs)) (orthantTemplate vs.length)

end JointThermoComplexity.Complexity.OffsetTemplateData

#print axioms JointThermoComplexity.Complexity.OffsetTemplateData.template_bounded
#print axioms JointThermoComplexity.Complexity.OffsetTemplateData.cube_total
#print axioms JointThermoComplexity.Complexity.OffsetTemplateData.orthant_total
