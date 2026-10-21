module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaCircuitData
public import proofs.JointThermoComplexity.Complexity.SourceTermCircuitSemantics

public import Mathlib.Tactic.FinCases

@[expose] public section

/- Adapted from DInstabilityComplexity/FormulaCircuitSoundness.lean in the private
D-stability completeness development. Original source and SHA-256 are
preserved in SOURCE_QUADRATIC_CIRCUIT_ADAPTATION.json and syntax-inputs/.
The original package Apache-2.0 license is retained in
third_party/quadratic-witness/LICENSE.original. This version uses only
the independently defined RealSyntax; no source-hardness theorem is assumed. -/

/-! # Activated formula circuits force the actual source formula's truth -/

namespace JointThermoComplexity.Complexity.QuadraticCircuit

variable {n : ℕ} {V W : Type}

open RealSyntax MvPolynomial

theorem atomLeft_assignment (s t : Term n) (ρ : Fin n → ℝ)
    (a : Unit ⊕ ((TermSlot s ⊕ TermSlot t) ⊕ Fin 3) → ℝ) :
    (Sum.elim ρ a) ∘ atomLeft s t = Sum.elim ρ (fun x => a (.inr (.inl (.inl x)))) := by
  funext v
  cases v <;> rfl

theorem atomRight_assignment (s t : Term n) (ρ : Fin n → ℝ)
    (a : Unit ⊕ ((TermSlot s ⊕ TermSlot t) ⊕ Fin 3) → ℝ) :
    (Sum.elim ρ a) ∘ atomRight s t = Sum.elim ρ (fun x => a (.inr (.inl (.inr x)))) := by
  funext v
  cases v <;> rfl

theorem equalityPorts_assignment (s t : Term n) (ρ : Fin n → ℝ)
    (a : Unit ⊕ ((TermSlot s ⊕ TermSlot t) ⊕ Fin 3) → ℝ) :
    (Sum.elim ρ a) ∘ atomEqualityPorts s t =
      ![a (.inl ()), a (.inr (.inl (.inl (termRoot s)))), a (.inr (.inl (.inr (termRoot t))))] := by
  funext i
  fin_cases i <;> rfl

theorem signPorts_assignment (s t : Term n) (ρ : Fin n → ℝ)
    (a : Unit ⊕ ((TermSlot s ⊕ TermSlot t) ⊕ Fin 3) → ℝ) :
    (Sum.elim ρ a) ∘ atomPorts s t =
      ![a (.inl ()), a (.inr (.inl (.inl (termRoot s)))), a (.inr (.inl (.inr (termRoot t)))),
        a (.inr (.inr 0)), a (.inr (.inr 1)), a (.inr (.inr 2))] := by
  funext i
  fin_cases i <;> rfl

theorem formulaLeft_assignment (p q : Formula n) (ρ : Fin n → ℝ)
    (a : Unit ⊕ (FormulaSlot p ⊕ FormulaSlot q) → ℝ) :
    (Sum.elim ρ a) ∘ formulaLeft p q = Sum.elim ρ (fun x => a (.inr (.inl x))) := by
  funext v
  cases v <;> rfl

theorem formulaRight_assignment (p q : Formula n) (ρ : Fin n → ℝ)
    (a : Unit ⊕ (FormulaSlot p ⊕ FormulaSlot q) → ℝ) :
    (Sum.elim ρ a) ∘ formulaRight p q = Sum.elim ρ (fun x => a (.inr (.inr x))) := by
  funext v
  cases v <;> rfl

theorem formulaEquations_sound (p : Formula n) (ρ : Fin n → ℝ) (a : FormulaSlot p → ℝ)
    (h : EquationsHold (formulaEquations p) (Sum.elim ρ a)) :
    BooleanBit (a (formulaRoot p)) ∧ (a (formulaRoot p) = 0 ∨ p.eval ρ) := by
  induction p with
  | truth =>
    have hb : BooleanBit (a ()) := by
      simpa [EquationsHold, formulaEquations, BooleanBit] using h
    exact ⟨hb, Or.inr trivial⟩
  | falsity =>
    have hz : a () = 0 := by simpa [EquationsHold, formulaEquations] using h
    exact ⟨(booleanBit_iff _).mpr (Or.inl hz), Or.inl hz⟩
  | eq s t =>
    rcases (equationsHold_append _ _ _).mp h with ⟨hlr, hg⟩
    rcases (equationsHold_append _ _ _).mp hlr with ⟨hl, hr⟩
    have hl' := (equationsHold_rename _ _ _).mp hl
    have hr' := (equationsHold_rename _ _ _).mp hr
    rw [atomLeft_assignment] at hl'
    rw [atomRight_assignment] at hr'
    have hs := termEquations_sound s ρ (fun x => a (.inr (.inl (.inl x)))) hl'
    have ht := termEquations_sound t ρ (fun x => a (.inr (.inl (.inr x)))) hr'
    have hg' := (equationsHold_rename _ _ _).mp hg
    rw [equalityPorts_assignment] at hg'
    have he := (equalityActivationEquations_iff _ _ _).mp hg'
    have hb := (equalityActivation_iff _ _ _).mp he
    simpa only [formulaRoot, Formula.eval, hs, ht] using hb
  | lt s t =>
    rcases (equationsHold_append _ _ _).mp h with ⟨hlr, hg⟩
    rcases (equationsHold_append _ _ _).mp hlr with ⟨hl, hr⟩
    have hl' := (equationsHold_rename _ _ _).mp hl
    have hr' := (equationsHold_rename _ _ _).mp hr
    rw [atomLeft_assignment] at hl'
    rw [atomRight_assignment] at hr'
    have hs := termEquations_sound s ρ (fun x => a (.inr (.inl (.inl x)))) hl'
    have ht := termEquations_sound t ρ (fun x => a (.inr (.inl (.inr x)))) hr'
    have hg' := (equationsHold_rename _ _ _).mp hg
    rw [signPorts_assignment] at hg'
    have he := (strictSignEquations_iff _ _ _ _ _ _).mp hg'
    have hb := strictSignActivation_sound he
    simpa only [formulaRoot, Formula.eval, hs, ht] using hb
  | conj p q hp hq =>
    rcases (equationsHold_append _ _ _).mp h with ⟨hlr, hg⟩
    rcases (equationsHold_append _ _ _).mp hlr with ⟨hl, hr⟩
    have hl' := (equationsHold_rename _ _ _).mp hl
    have hr' := (equationsHold_rename _ _ _).mp hr
    rw [formulaLeft_assignment] at hl'
    rw [formulaRight_assignment] at hr'
    have hp' := hp (fun x => a (.inr (.inl x))) hl'
    have hq' := hq (fun x => a (.inr (.inr x))) hr'
    have hg' : BooleanBit (a (.inl ())) ∧
        a (.inr (.inl (formulaRoot p))) = a (.inl ()) ∧
          a (.inr (.inr (formulaRoot q))) = a (.inl ()) := by
      simpa [EquationsHold, BooleanBit, sub_eq_zero] using hg
    rw [hg'.2.1] at hp'
    rw [hg'.2.2] at hq'
    refine ⟨hg'.1, ?_⟩
    rcases hp'.2 with hz | hP
    · exact Or.inl hz
    · rcases hq'.2 with hz | hQ
      · exact Or.inl hz
      · exact Or.inr ⟨hP, hQ⟩
  | disj p q hp hq =>
    rcases (equationsHold_append _ _ _).mp h with ⟨hlr, hg⟩
    rcases (equationsHold_append _ _ _).mp hlr with ⟨hl, hr⟩
    have hl' := (equationsHold_rename _ _ _).mp hl
    have hr' := (equationsHold_rename _ _ _).mp hr
    rw [formulaLeft_assignment] at hl'
    rw [formulaRight_assignment] at hr'
    have hp' := hp (fun x => a (.inr (.inl x))) hl'
    have hq' := hq (fun x => a (.inr (.inr x))) hr'
    have hg' : BooleanBit (a (.inl ())) ∧
        a (.inr (.inl (formulaRoot p))) + a (.inr (.inr (formulaRoot q))) = a (.inl ()) := by
      simpa [EquationsHold, BooleanBit, sub_eq_zero] using hg
    refine ⟨hg'.1, ?_⟩
    rcases hp'.2 with hb | hP
    · rcases hq'.2 with hc | hQ
      · left
        have he := hg'.2
        rw [hb, hc, zero_add] at he
        exact he.symm
      · exact Or.inr (Or.inr hQ)
    · exact Or.inr (Or.inl hP)

#print axioms formulaEquations_sound

end JointThermoComplexity.Complexity.QuadraticCircuit
