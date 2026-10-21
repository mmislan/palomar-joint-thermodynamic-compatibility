module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaCircuitData
public import proofs.JointThermoComplexity.Complexity.SourceTermCircuitDegree

@[expose] public section

/- Adapted from DInstabilityComplexity/FormulaCircuitDegree.lean in the private
D-stability completeness development. Original source and SHA-256 are
preserved in SOURCE_QUADRATIC_CIRCUIT_ADAPTATION.json and syntax-inputs/.
The original package Apache-2.0 license is retained in
third_party/quadratic-witness/LICENSE.original. This version uses only
the independently defined RealSyntax; no source-hardness theorem is assumed. -/

/-! # Degree bounds for every equation of the complete formula circuit -/

namespace JointThermoComplexity.Complexity.QuadraticCircuit

variable {n : ℕ} {V W : Type}

open RealSyntax MvPolynomial

private theorem variable_linear (v : V) : (X v : MvPolynomial V ℤ).totalDegree ≤ 1 :=
  le_of_eq (MvPolynomial.totalDegree_X v)

private theorem variable_difference_linear (v w : V) :
    (X v - X w : MvPolynomial V ℤ).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_sub _ _).trans (max_le (variable_linear _) (variable_linear _))

private theorem boolean_equation_quadratic (v : V) :
    (X v * (X v - 1) : MvPolynomial V ℤ).totalDegree ≤ 2 := by
  apply (MvPolynomial.totalDegree_mul _ _).trans
  exact Nat.add_le_add (variable_linear _)
    ((MvPolynomial.totalDegree_sub _ _).trans (max_le (variable_linear _) (by simp)))

theorem formulaEquations_quadratic (p : Formula n) (f : MvPolynomial (Fin n ⊕ FormulaSlot p) ℤ)
    (hf : f ∈ formulaEquations p) : f.totalDegree ≤ 2 := by
  induction p with
  | truth =>
    have he := List.mem_singleton.mp hf
    rw [he]
    exact boolean_equation_quadratic _
  | falsity =>
    have he := List.mem_singleton.mp hf
    rw [he]
    exact (variable_linear _).trans (by decide : 1 ≤ 2)
  | eq s t =>
    rcases List.mem_append.mp hf with hlr | hg
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
        exact (MvPolynomial.totalDegree_rename_le _ _).trans (termEquations_quadratic s q hq)
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact (MvPolynomial.totalDegree_rename_le _ _).trans (termEquations_quadratic t q hq)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
      exact (MvPolynomial.totalDegree_rename_le _ _).trans (equalityActivationEquations_quadratic q hq)
  | lt s t =>
    rcases List.mem_append.mp hf with hlr | hg
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
        exact (MvPolynomial.totalDegree_rename_le _ _).trans (termEquations_quadratic s q hq)
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact (MvPolynomial.totalDegree_rename_le _ _).trans (termEquations_quadratic t q hq)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
      exact (MvPolynomial.totalDegree_rename_le _ _).trans (strictSignEquations_quadratic q hq)
  | conj p q hp hq =>
    rcases List.mem_append.mp hf with hlr | hout
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hl
        exact (MvPolynomial.totalDegree_rename_le _ _).trans (hp g hg)
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
        exact (MvPolynomial.totalDegree_rename_le _ _).trans (hq g hg)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
      rcases hout with rfl | rfl | rfl
      · exact boolean_equation_quadratic _
      · exact (variable_difference_linear _ _).trans (by decide : 1 ≤ 2)
      · exact (variable_difference_linear _ _).trans (by decide : 1 ≤ 2)
  | disj p q hp hq =>
    rcases List.mem_append.mp hf with hlr | hout
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hl
        exact (MvPolynomial.totalDegree_rename_le _ _).trans (hp g hg)
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
        exact (MvPolynomial.totalDegree_rename_le _ _).trans (hq g hg)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
      rcases hout with rfl | rfl
      · exact boolean_equation_quadratic _
      · apply (MvPolynomial.totalDegree_sub _ _).trans
        apply max_le _ ((variable_linear _).trans (by decide : 1 ≤ 2))
        exact (MvPolynomial.totalDegree_add _ _).trans
          (max_le ((variable_linear _).trans (by decide : 1 ≤ 2))
            ((variable_linear _).trans (by decide : 1 ≤ 2)))

#print axioms formulaEquations_quadratic

end JointThermoComplexity.Complexity.QuadraticCircuit
