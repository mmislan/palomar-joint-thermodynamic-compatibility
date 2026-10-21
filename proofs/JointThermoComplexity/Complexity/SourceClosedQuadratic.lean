module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaCircuitExtension
public import proofs.JointThermoComplexity.Complexity.SourceFormulaCircuitDegree
public import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
@[expose] public section

/-! # Independent source sentences as finite integer quadratic systems

The activation-root argument follows the D-stability development's
ClosedQuadraticFormula.lean. Original sources and attribution are retained in
the private adaptation record. Here declared variables already have unary
headers, so no compression or foreign formula model is needed. The finite
reindexing below is a semantic definition, not a binary runtime theorem.
-/

namespace JointThermoComplexity.Complexity.QuadraticCircuit
open RealSyntax MvPolynomial
variable {n : ℕ}

noncomputable def closedFormulaEquations (p : Formula n) :
    List (MvPolynomial (Fin n ⊕ FormulaSlot p) ℤ) :=
  formulaEquations p ++ [X (.inr (formulaRoot p)) - 1]

theorem closedFormulaEquations_satisfiable_iff (p : Formula n) :
    (∃ x : Fin n ⊕ FormulaSlot p → ℝ, EquationsHold (closedFormulaEquations p) x) ↔
      ∃ ρ, p.eval ρ := by
  constructor
  · rintro ⟨x, hx⟩
    rcases (equationsHold_append _ _ _).mp hx with ⟨hc, hr⟩
    have hroot : x (.inr (formulaRoot p)) = 1 := by
      simpa [equationsHold_singleton, sub_eq_zero] using hr
    let ρ : Fin n → ℝ := fun v => x (.inl v)
    let a : FormulaSlot p → ℝ := fun v => x (.inr v)
    have he : Sum.elim ρ a = x := by funext v; cases v <;> rfl
    have hs := formulaEquations_sound p ρ a (by rw [he]; exact hc)
    have ha : a (formulaRoot p) = 1 := hroot
    rw [ha] at hs
    exact ⟨ρ, hs.2.resolve_left (by norm_num)⟩
  · rintro ⟨ρ, hp⟩
    obtain ⟨a, ha, har⟩ := formulaEquations_extension p ρ 1
      (by norm_num [BooleanBit]) (Or.inr hp)
    refine ⟨Sum.elim ρ a, (equationsHold_append _ _ _).mpr ⟨ha, ?_⟩⟩
    simp [equationsHold_singleton, har]

theorem closedFormulaEquations_quadratic (p : Formula n)
    (f : MvPolynomial (Fin n ⊕ FormulaSlot p) ℤ) (hf : f ∈ closedFormulaEquations p) :
    f.totalDegree ≤ 2 := by
  rcases List.mem_append.mp hf with h | h
  · exact formulaEquations_quadratic p f h
  · have he := List.mem_singleton.mp h
    rw [he]
    exact (MvPolynomial.totalDegree_sub _ _).trans (max_le
      ((le_of_eq (MvPolynomial.totalDegree_X _)).trans (by decide : 1 ≤ 2)) (by simp))

theorem closedFormulaEquations_length_le (p : Formula n) :
    (closedFormulaEquations p).length ≤ 4 * p.size + 1 := by
  rw [closedFormulaEquations, List.length_append]
  exact Nat.add_le_add_right (formulaEquations_length_le p) 1

abbrev SourceVariables (s : Sentence) := Fin s.arity ⊕ FormulaSlot s.formula

def sourceArity (s : Sentence) : ℕ := Fintype.card (SourceVariables s)

noncomputable def sourceReindex (s : Sentence) : SourceVariables s ≃ Fin (sourceArity s) :=
  Fintype.equivFin _

noncomputable def sourceEquations (s : Sentence) :
    List (MvPolynomial (Fin (sourceArity s)) ℤ) :=
  (closedFormulaEquations s.formula).map (rename (sourceReindex s))

theorem sourceEquations_satisfiable_iff (s : Sentence) :
    (∃ x, EquationsHold (sourceEquations s) x) ↔ s.Satisfiable := by
  constructor
  · rintro ⟨x, hx⟩
    exact (closedFormulaEquations_satisfiable_iff s.formula).mp
      ⟨x ∘ sourceReindex s, (equationsHold_rename _ _ _).mp hx⟩
  · intro hs
    obtain ⟨x, hx⟩ := (closedFormulaEquations_satisfiable_iff s.formula).mpr hs
    refine ⟨x ∘ (sourceReindex s).symm, (equationsHold_rename _ _ _).mpr ?_⟩
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hx

theorem sourceEquations_quadratic (s : Sentence)
    (f : MvPolynomial (Fin (sourceArity s)) ℤ) (hf : f ∈ sourceEquations s) :
    f.totalDegree ≤ 2 := by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (closedFormulaEquations_quadratic s.formula g hg)

theorem sourceArity_le_code_length (s : Sentence) : sourceArity s ≤ 5 * s.code.length := by
  have ha := RealSyntax.variables_le_code_length s
  have hb := card_formulaSlot_le s.formula
  have hc := s.formula.size_le_code_length
  have hd : s.formula.code.length ≤ s.code.length := by
    simp only [Sentence.code, List.length_append]
    omega
  unfold sourceArity
  rw [Fintype.card_sum, Fintype.card_fin]
  omega

theorem sourceEquations_length_le_code_length (s : Sentence) :
    (sourceEquations s).length ≤ 4 * s.code.length + 1 := by
  have hb := closedFormulaEquations_length_le s.formula
  have hc := s.formula.size_le_code_length
  have hd : s.formula.code.length ≤ s.code.length := by
    simp only [Sentence.code, List.length_append]
    omega
  rw [sourceEquations, List.length_map]
  omega

end JointThermoComplexity.Complexity.QuadraticCircuit

#print axioms JointThermoComplexity.Complexity.QuadraticCircuit.sourceEquations_satisfiable_iff
#print axioms JointThermoComplexity.Complexity.QuadraticCircuit.sourceEquations_quadratic
#print axioms JointThermoComplexity.Complexity.QuadraticCircuit.sourceArity_le_code_length
#print axioms JointThermoComplexity.Complexity.QuadraticCircuit.sourceEquations_length_le_code_length
