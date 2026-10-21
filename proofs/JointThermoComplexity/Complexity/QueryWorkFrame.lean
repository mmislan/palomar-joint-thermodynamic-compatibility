module
public import proofs.JointThermoComplexity.Complexity.RelocatedSpanQuery

set_option autoImplicit false
@[expose] public section

/-! Physical query readiness excludes the temporarily changing cursor-position tape. -/

namespace JointThermoComplexity.Complexity.QueryWorkFrame
open _root_.Complexity _root_.Complexity.TM EquationQueryLayout RelocatedSpanQuery

def tags (i : Fin 3) : Fin 32 := ⟨i.val + 8, by omega⟩
def pending : Fin 32 := ⟨11, by decide⟩
def fuel : Fin 32 := ⟨12, by decide⟩
def result : Fin 32 := ⟨13, by decide⟩
def flag : Fin 32 := ⟨14, by decide⟩
def formulas : Fin 32 := ⟨15, by decide⟩
def position : Fin 32 := ⟨17, by decide⟩

def Outside (j : Fin 32) : Prop := ((∃ i, j = main i) ∨ 16 ≤ j.val) ∧ j ≠ position

def Stable (R : Work → Prop) : Prop :=
  ∀ work work', (∀ j, Outside j → work' j = work j) → R work → R work'

structure Ready (tp fp nodes budget : ℕ) (R : Work → Prop) (work : Work) : Prop where
  markers : ∀ j, j ≠ position → (work j).cells 0 = Γ.start
  tagHeads : ∀ i, (work (tags i)).head = 1
  flagHead : (work flag).head = 1
  termReg : IsReg tp (work pending)
  formulaReg : IsReg fp (work formulas)
  nodeReg : IsReg nodes (work result)
  fuelReg : IsReg budget (work fuel)
  frame : R work

theorem stable_position (R : Work → Prop) (hR : Stable R) :
    ∀ work work', (∀ j, j ≠ position → work' j = work j) → R work → R work' :=
  fun work work' he => hR work work' (fun j hj => he j hj.2)

theorem ready_position (tp fp nodes budget : ℕ) (R : Work → Prop) (hR : Stable R) :
    ∀ work work', (∀ j, j ≠ position → work' j = work j) →
      Ready tp fp nodes budget R work → Ready tp fp nodes budget R work' := by
  rintro work work' he hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, stable_position R hR work work' he hr.frame⟩
  · intro j hj
    simpa only [he j hj] using hr.markers j hj
  · intro i
    have hi : tags i ≠ position := by intro h; have := congrArg Fin.val h; change i.val + 8 = 17 at this; omega
    simpa only [he _ hi] using hr.tagHeads i
  · simpa only [he _ (by decide : flag ≠ position)] using hr.flagHead
  · simpa only [he _ (by decide : pending ≠ position)] using hr.termReg
  · simpa only [he _ (by decide : formulas ≠ position)] using hr.formulaReg
  · simpa only [he _ (by decide : result ≠ position)] using hr.nodeReg
  · simpa only [he _ (by decide : fuel ≠ position)] using hr.fuelReg

def unview (work : Work) : Work := fun j => work (permutation.symm j)

theorem unview_view (work : Work) : unview (view work) = work := by
  funext j
  simp only [unview, view, Equiv.apply_symm_apply]

theorem term_outside (j : Fin 32) (hj : Outside j) :
    TermSpanRegisters.Outside 25 (permutation.symm j) ∧ permutation.symm j ≠ TermSpanRegisters.fuel 25 := by
  rcases hj.1 with ⟨i, rfl⟩ | hh
  · exact main_term_outside i
  · exact high_term_outside j hh

theorem formula_outside (j : Fin 32) (hj : Outside j) :
    FormulaSpanRegisters.Outside 24 (permutation.symm j) ∧ permutation.symm j ≠ FormulaSpanLoop.fuel 24 := by
  rcases hj.1 with ⟨i, rfl⟩ | hh
  · exact main_formula_outside i
  · exact high_formula_outside j hh

theorem term_tags : ∀ i, permutation (TermSpanRegisters.tags 25 i) = tags i := by decide

theorem term_position_outside : TermSpanRegisters.Outside 25 (permutation.symm position) ∧
    permutation.symm position ≠ TermSpanRegisters.fuel 25 := high_term_outside position (by decide)

theorem term_formulas_outside : TermSpanRegisters.Outside 25 (permutation.symm formulas) ∧
    permutation.symm formulas ≠ TermSpanRegisters.fuel 25 := by unfold TermSpanRegisters.Outside; decide

theorem formula_position_outside : FormulaSpanRegisters.Outside 24 (permutation.symm position) ∧
    permutation.symm position ≠ FormulaSpanLoop.fuel 24 := high_formula_outside position (by decide)

def TermExtra (p fp : ℕ) (R : Work → Prop) (work : Work) : Prop :=
  IsReg p (unview work position) ∧ IsReg fp (unview work formulas) ∧ R (unview work)

def FormulaExtra (p : ℕ) (R : Work → Prop) (work : Work) : Prop :=
  IsReg p (unview work position) ∧ R (unview work)

theorem term_extra_stable (p fp : ℕ) (R : Work → Prop) (hR : Stable R) :
    TermSpanLoop.Stable (TermExtra p fp R) := by
  rintro work work' he ⟨hp, hf, hr⟩
  exact ⟨by simpa only [TermExtra, unview, he _ term_position_outside.1 term_position_outside.2] using hp,
    by simpa only [unview, he _ term_formulas_outside.1 term_formulas_outside.2] using hf,
    hR (unview work) (unview work') (fun j hj => he _ (term_outside j hj).1 (term_outside j hj).2) hr⟩

theorem formula_extra_stable (p : ℕ) (R : Work → Prop) (hR : Stable R) :
    FormulaSpanLoop.Stable (FormulaExtra p R) := by
  rintro work work' he ⟨hp, hr⟩
  exact ⟨by simpa only [unview, he _ formula_position_outside.1 formula_position_outside.2] using hp,
    hR (unview work) (unview work') (fun j hj => he _ (formula_outside j hj).1 (formula_outside j hj).2) hr⟩

end JointThermoComplexity.Complexity.QueryWorkFrame

#print axioms JointThermoComplexity.Complexity.QueryWorkFrame.ready_position
#print axioms JointThermoComplexity.Complexity.QueryWorkFrame.term_extra_stable
#print axioms JointThermoComplexity.Complexity.QueryWorkFrame.formula_extra_stable
