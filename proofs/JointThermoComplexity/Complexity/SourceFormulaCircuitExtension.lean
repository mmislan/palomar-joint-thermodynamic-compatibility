module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaCircuitSoundness

@[expose] public section

/- Adapted from DInstabilityComplexity/FormulaCircuitExtension.lean in the private
D-stability completeness development. Original source and SHA-256 are
preserved in SOURCE_QUADRATIC_CIRCUIT_ADAPTATION.json and syntax-inputs/.
The original package Apache-2.0 license is retained in
third_party/quadratic-witness/LICENSE.original. This version uses only
the independently defined RealSyntax; no source-hardness theorem is assumed. -/

/-! # Every valid activation of a source formula extends to its quadratic circuit -/

namespace JointThermoComplexity.Complexity.QuadraticCircuit

variable {n : ℕ} {V W : Type}

open RealSyntax MvPolynomial

def atomCombined (s t : Term n) (ρ : Fin n → ℝ) (r : ℝ) (w : Fin 3 → ℝ) :
    Unit ⊕ ((TermSlot s ⊕ TermSlot t) ⊕ Fin 3) → ℝ :=
  Sum.elim (fun _ => r) (Sum.elim (Sum.elim (termValues ρ s) (termValues ρ t)) w)

def formulaCombined (p q : Formula n) (r : ℝ) (a : FormulaSlot p → ℝ) (b : FormulaSlot q → ℝ) :
    Unit ⊕ (FormulaSlot p ⊕ FormulaSlot q) → ℝ :=
  Sum.elim (fun _ => r) (Sum.elim a b)

theorem atomCombined_left (s t : Term n) (ρ : Fin n → ℝ) (r : ℝ) (w : Fin 3 → ℝ) :
    EquationsHold ((termEquations s).map (rename (atomLeft s t)))
      (Sum.elim ρ (atomCombined s t ρ r w)) := by
  apply (equationsHold_rename _ _ _).mpr
  rw [atomLeft_assignment]
  exact termEquations_extension s ρ

theorem atomCombined_right (s t : Term n) (ρ : Fin n → ℝ) (r : ℝ) (w : Fin 3 → ℝ) :
    EquationsHold ((termEquations t).map (rename (atomRight s t)))
      (Sum.elim ρ (atomCombined s t ρ r w)) := by
  apply (equationsHold_rename _ _ _).mpr
  rw [atomRight_assignment]
  exact termEquations_extension t ρ

private theorem boolean_partition_extension (P Q : Prop) (r : ℝ) (hr : BooleanBit r)
    (h : r = 0 ∨ P ∨ Q) :
    ∃ b c : ℝ, BooleanBit b ∧ BooleanBit c ∧ b + c = r ∧ (b = 0 ∨ P) ∧ (c = 0 ∨ Q) := by
  rcases (booleanBit_iff r).mp hr with rfl | rfl
  · refine ⟨0, 0, ?_, ?_, by norm_num, Or.inl rfl, Or.inl rfl⟩ <;> norm_num [BooleanBit]
  · have hpq : P ∨ Q := h.resolve_left (by norm_num)
    rcases hpq with hp | hq
    · refine ⟨1, 0, ?_, ?_, by norm_num, Or.inr hp, Or.inl rfl⟩ <;> norm_num [BooleanBit]
    · refine ⟨0, 1, ?_, ?_, by norm_num, Or.inl rfl, Or.inr hq⟩ <;> norm_num [BooleanBit]

theorem formulaEquations_extension (p : Formula n) (ρ : Fin n → ℝ) (r : ℝ)
    (hr : BooleanBit r) (h : r = 0 ∨ p.eval ρ) :
    ∃ a : FormulaSlot p → ℝ, EquationsHold (formulaEquations p) (Sum.elim ρ a) ∧ a (formulaRoot p) = r := by
  induction p generalizing r with
  | truth =>
    refine ⟨fun _ => r, ?_, rfl⟩
    simpa [EquationsHold, formulaEquations, BooleanBit] using hr
  | falsity =>
    have hz : r = 0 := h.elim id False.elim
    subst r
    refine ⟨fun _ => 0, ?_, rfl⟩
    simp [EquationsHold, formulaEquations]
  | eq s t =>
    refine ⟨atomCombined s t ρ r (fun _ => 0), ?_, rfl⟩
    apply (equationsHold_append _ _ _).mpr
    refine ⟨(equationsHold_append _ _ _).mpr ⟨atomCombined_left s t ρ r _, atomCombined_right s t ρ r _⟩, ?_⟩
    apply (equationsHold_rename _ _ _).mpr
    rw [equalityPorts_assignment]
    simp only [atomCombined, Sum.elim_inl, Sum.elim_inr, termValues_root]
    apply (equalityActivationEquations_iff _ _ _).mpr
    refine ⟨hr, ?_⟩
    rcases h with hz | he
    · rw [hz, zero_mul]
    · rw [he, sub_self, mul_zero]
  | lt s t =>
    obtain ⟨y, b, c, hg⟩ := strictSignActivation_extension r (s.eval ρ) (t.eval ρ) hr h
    refine ⟨atomCombined s t ρ r ![y, b, c], ?_, rfl⟩
    apply (equationsHold_append _ _ _).mpr
    refine ⟨(equationsHold_append _ _ _).mpr ⟨atomCombined_left s t ρ r _, atomCombined_right s t ρ r _⟩, ?_⟩
    apply (equationsHold_rename _ _ _).mpr
    rw [signPorts_assignment]
    simp only [atomCombined, Sum.elim_inl, Sum.elim_inr, termValues_root]
    exact (strictSignEquations_iff _ _ _ _ _ _).mpr hg
  | conj p q hp hq =>
    have hP : r = 0 ∨ p.eval ρ := h.elim Or.inl (fun hPQ => Or.inr hPQ.1)
    have hQ : r = 0 ∨ q.eval ρ := h.elim Or.inl (fun hPQ => Or.inr hPQ.2)
    obtain ⟨a, ha, har⟩ := hp r hr hP
    obtain ⟨b, hb, hbr⟩ := hq r hr hQ
    refine ⟨formulaCombined p q r a b, ?_, rfl⟩
    apply (equationsHold_append _ _ _).mpr
    refine ⟨(equationsHold_append _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
    · apply (equationsHold_rename _ _ _).mpr
      rw [formulaLeft_assignment]
      exact ha
    · apply (equationsHold_rename _ _ _).mpr
      rw [formulaRight_assignment]
      exact hb
    · simpa [EquationsHold, formulaCombined, BooleanBit, har, hbr] using hr
  | disj p q hp hq =>
    obtain ⟨u, v, hu, hv, huv, hP, hQ⟩ := boolean_partition_extension (p.eval ρ) (q.eval ρ) r hr h
    obtain ⟨a, ha, har⟩ := hp u hu hP
    obtain ⟨b, hb, hbr⟩ := hq v hv hQ
    refine ⟨formulaCombined p q r a b, ?_, rfl⟩
    apply (equationsHold_append _ _ _).mpr
    refine ⟨(equationsHold_append _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
    · apply (equationsHold_rename _ _ _).mpr
      rw [formulaLeft_assignment]
      exact ha
    · apply (equationsHold_rename _ _ _).mpr
      rw [formulaRight_assignment]
      exact hb
    · simpa [EquationsHold, formulaCombined, BooleanBit, har, hbr, sub_eq_zero, huv] using hr

theorem formula_circuit_exact (p : Formula n) (ρ : Fin n → ℝ) (r : ℝ) :
    (∃ a : FormulaSlot p → ℝ, EquationsHold (formulaEquations p) (Sum.elim ρ a) ∧ a (formulaRoot p) = r) ↔
      BooleanBit r ∧ (r = 0 ∨ p.eval ρ) := by
  constructor
  · rintro ⟨a, ha, har⟩
    have hs := formulaEquations_sound p ρ a ha
    simpa only [har] using hs
  · rintro ⟨hr, h⟩
    exact formulaEquations_extension p ρ r hr h

#print axioms formulaEquations_extension
#print axioms formula_circuit_exact

end JointThermoComplexity.Complexity.QuadraticCircuit
