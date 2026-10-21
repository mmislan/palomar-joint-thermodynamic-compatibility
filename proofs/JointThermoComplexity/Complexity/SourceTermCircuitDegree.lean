module
public import proofs.JointThermoComplexity.Complexity.SourceTermCircuitData
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

/- Adapted from DInstabilityComplexity/TermCircuitDegree.lean in the private
D-stability completeness development. Original source and SHA-256 are
preserved in SOURCE_QUADRATIC_CIRCUIT_ADAPTATION.json and syntax-inputs/.
The original package Apache-2.0 license is retained in
third_party/quadratic-witness/LICENSE.original. This version uses only
the independently defined RealSyntax; no source-hardness theorem is assumed. -/

/-! # All generated operation equations have total degree at most two -/

namespace JointThermoComplexity.Complexity.QuadraticCircuit

variable {n : ℕ} {V W : Type}

open RealSyntax MvPolynomial

private theorem variable_degree_le_two (v : V) : (X v : MvPolynomial V ℤ).totalDegree ≤ 2 := by
  rw [MvPolynomial.totalDegree_X]
  decide

theorem termEquations_quadratic (t : Term n) (p : MvPolynomial (Fin n ⊕ TermSlot t) ℤ)
    (hp : p ∈ termEquations t) : p.totalDegree ≤ 2 := by
  induction t with
  | int z =>
    have he : p = X (.inr ()) - C z := List.mem_singleton.mp hp
    rw [he]
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (variable_degree_le_two _) (by rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _))
  | var v =>
    have he : p = X (.inr ()) - X (.inl v) := List.mem_singleton.mp hp
    rw [he]
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (variable_degree_le_two _) (variable_degree_le_two _))
  | add s t hs ht =>
    rcases List.mem_append.mp hp with hlr | hout
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
        exact (MvPolynomial.totalDegree_rename_le _ _).trans (hs q hq)
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact (MvPolynomial.totalDegree_rename_le _ _).trans (ht q hq)
    · have he := List.mem_singleton.mp hout
      rw [he]
      exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (variable_degree_le_two _)
        ((MvPolynomial.totalDegree_add _ _).trans
          (max_le (variable_degree_le_two _) (variable_degree_le_two _))))
  | mul s t hs ht =>
    rcases List.mem_append.mp hp with hlr | hout
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
        exact (MvPolynomial.totalDegree_rename_le _ _).trans (hs q hq)
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact (MvPolynomial.totalDegree_rename_le _ _).trans (ht q hq)
    · have he := List.mem_singleton.mp hout
      rw [he]
      apply (MvPolynomial.totalDegree_sub _ _).trans
      apply max_le (variable_degree_le_two _)
      simpa only [MvPolynomial.totalDegree_X] using (MvPolynomial.totalDegree_mul
        (X (.inr (.inr (.inl (termRoot s)))) : MvPolynomial (Fin n ⊕ TermSlot (.mul s t)) ℤ)
        (X (.inr (.inr (.inr (termRoot t))))))
  | neg s hs =>
    rcases List.mem_append.mp hp with hl | hout
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
      exact (MvPolynomial.totalDegree_rename_le _ _).trans (hs q hq)
    · have he := List.mem_singleton.mp hout
      rw [he]
      exact (MvPolynomial.totalDegree_add _ _).trans
        (max_le (variable_degree_le_two _) (variable_degree_le_two _))

theorem card_termCircuitVariables (t : Term n) :
    Fintype.card (Fin n ⊕ TermSlot t) = n + t.size := by
  rw [Fintype.card_sum, Fintype.card_fin, card_termSlot]

#print axioms termEquations_quadratic
#print axioms card_termCircuitVariables

end JointThermoComplexity.Complexity.QuadraticCircuit
