module
public import proofs.JointThermoComplexity.Complexity.RawNormalizationTemplates
public import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
@[expose] public section

/-! A finite static normalization table at degree four. The source coefficient
is scaled by one of five fixed positive magnitudes in the boxed case and by
one in the orthant case; variable occurrences remain explicit template slots. -/

namespace JointThermoComplexity.Complexity.DegreeFourTemplates
open SparseInteger SparseSubstitution RawNormalizationTemplates

def cubeCoefficients : List ℤ := [16, -24, 36, -54, 81]
def orthantCoefficients : List ℤ := [1, -1]

theorem cube_all (m : ℕ) (hm : m ≤ 4) :
    (cubeTemplate 4 m).all (fun a => decide (a.1 ∈ cubeCoefficients)) = true := by
  interval_cases m <;> decide

theorem orthant_all (m : ℕ) (hm : m ≤ 4) :
    (orthantTemplate m).all (fun a => decide (a.1 ∈ orthantCoefficients)) = true := by
  interval_cases m <;> decide

theorem cube_coefficient (m : ℕ) (hm : m ≤ 4) (a : ℤ × List (Fin m)) (ha : a ∈ cubeTemplate 4 m) :
    a.1 ∈ cubeCoefficients := by
  exact of_decide_eq_true ((List.all_eq_true.mp (cube_all m hm)) a ha)

theorem orthant_coefficient (m : ℕ) (hm : m ≤ 4) (a : ℤ × List (Fin m ⊕ Fin m)) (ha : a ∈ orthantTemplate m) :
    a.1 ∈ orthantCoefficients := by
  exact of_decide_eq_true ((List.all_eq_true.mp (orthant_all m hm)) a ha)

theorem cube_magnitude_choices (m : ℕ) (hm : m ≤ 4) (a : ℤ × List (Fin m)) (ha : a ∈ cubeTemplate 4 m) :
    a.1.natAbs ∈ ([16, 24, 36, 54, 81] : List ℕ) := by
  have h : a.1.natAbs ∈ cubeCoefficients.map Int.natAbs :=
    List.mem_map.mpr ⟨a.1, cube_coefficient m hm a ha, rfl⟩
  simpa [cubeCoefficients] using h

theorem cube_magnitude_bounds (m : ℕ) (hm : m ≤ 4) (a : ℤ × List (Fin m)) (ha : a ∈ cubeTemplate 4 m) :
    0 < a.1.natAbs ∧ a.1.natAbs ≤ 81 := by
  have h := cube_magnitude_choices m hm a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem orthant_magnitude (m : ℕ) (hm : m ≤ 4) (a : ℤ × List (Fin m ⊕ Fin m)) (ha : a ∈ orthantTemplate m) :
    a.1.natAbs = 1 := by
  have hc := orthant_coefficient m hm a ha
  simp only [orthantCoefficients, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with hc | hc <;> rw [hc] <;> rfl

theorem cube_length_le (m : ℕ) (hm : m ≤ 4) : (cubeTemplate 4 m).length ≤ 16 := by
  rw [length_cubeTemplate]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm

theorem orthant_length_le (m : ℕ) (hm : m ≤ 4) : (orthantTemplate m).length ≤ 16 := by
  rw [length_orthantTemplate]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm

theorem cubeTerm_member {V : Type} (c : ℤ) (vs : List V) (a : ℤ × List V) (ha : a ∈ cubeTerm 4 (c, vs)) :
    ∃ t ∈ cubeTemplate 4 vs.length, a = (c * t.1, t.2.map (lookup vs)) := by
  rw [cubeTerm_from_template] at ha
  simp only [scale, relabel, List.map_map, List.mem_map] at ha
  obtain ⟨t, ht, he⟩ := ha
  exact ⟨t, ht, he.symm⟩

end JointThermoComplexity.Complexity.DegreeFourTemplates

#print axioms JointThermoComplexity.Complexity.DegreeFourTemplates.cube_all
#print axioms JointThermoComplexity.Complexity.DegreeFourTemplates.orthant_all
#print axioms JointThermoComplexity.Complexity.DegreeFourTemplates.cube_magnitude_bounds
#print axioms JointThermoComplexity.Complexity.DegreeFourTemplates.cubeTerm_member
