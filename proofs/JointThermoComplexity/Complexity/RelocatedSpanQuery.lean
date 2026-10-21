module
public import proofs.JointThermoComplexity.Complexity.EquationQueryLayout
public import proofs.JointThermoComplexity.Complexity.WorkPermutation

set_option autoImplicit false
@[expose] public section

/-! Actual subtree counters run on query ports while protecting main and later scratch tapes. -/

namespace JointThermoComplexity.Complexity.RelocatedSpanQuery
open _root_.Complexity _root_.Complexity.TM HeaderAt EquationQueryLayout

abbrev Work := Fin 32 → Tape

def view (work : Work) : Work := fun j => work (permutation j)

def termMachine : TM 32 := WorkPermutation.machine permutation (TermSpanLoop.machine 25)
def formulaMachine : TM 32 := WorkPermutation.machine permutation (FormulaSpanLoop.machine 24)

def TermInv (emitted : List Bool) (R : Work → Prop) (s : TermSpanControl.State) :
    _root_.Complexity.TM.TapePred 32 := fun inp work out => TermSpanRegisters.Inv emitted R s inp (view work) out

def FormulaInv (emitted : List Bool) (R : Work → Prop) (s : FormulaSpanControl.State) :
    _root_.Complexity.TM.TapePred 32 := fun inp work out => FormulaSpanRegisters.Inv emitted R s inp (view work) out

def ProtectedFrame (saved : Work) (work : Work) : Prop :=
  (∀ i, work (permutation.symm (main i)) = saved (main i)) ∧
  (∀ j, 16 ≤ j.val → work (permutation.symm j) = saved j)

theorem term_frame_stable (saved : Work) : TermSpanLoop.Stable (ProtectedFrame saved) := by
  rintro work work' he ⟨hm, hh⟩
  exact ⟨fun i => (he _ (main_term_outside i).1 (main_term_outside i).2).trans (hm i),
    fun j hj => (he _ (high_term_outside j hj).1 (high_term_outside j hj).2).trans (hh j hj)⟩

theorem formula_frame_stable (saved : Work) : FormulaSpanLoop.Stable (ProtectedFrame saved) := by
  rintro work work' he ⟨hm, hh⟩
  exact ⟨fun i => (he _ (main_formula_outside i).1 (main_formula_outside i).2).trans (hm i),
    fun j hj => (he _ (high_formula_outside j hj).1 (high_formula_outside j hj).2).trans (hh j hj)⟩

theorem physical_frame (saved work : Work) (h : ProtectedFrame saved (view work)) :
    (∀ i, work (main i) = saved (main i)) ∧ (∀ j, 16 ≤ j.val → work j = saved j) := by
  simpa only [ProtectedFrame, view, Equiv.apply_symm_apply] using h

theorem physical_cursor {before input emitted : List Bool} {inp out : Tape} {work : Work}
    (hc : Cursor before input emitted inp (view work) out) : Cursor before input emitted inp work out := by
  refine ⟨hc.cells, hc.head, ?_, hc.tapePrefix, hc.zero⟩
  intro j
  simpa only [view, Equiv.apply_symm_apply] using hc.works (permutation.symm j)

theorem term_hoareTime (L count : ℕ) (emitted : List Bool) (R : Work → Prop)
    (hR : TermSpanLoop.Stable R) (s : TermSpanControl.State) (hlen : s.input.length ≤ L) :
    termMachine.HoareTime
      (fun inp work out => TermInv emitted R s inp work out ∧
        IsReg count (work (permutation (TermSpanRegisters.fuel 25))))
      (fun inp work out => TermInv emitted R (TermSpanControl.run count s) inp work out ∧
        IsReg count (work (permutation (TermSpanRegisters.fuel 25))))
      (TermSpanLoop.timeBound L s.pending s.nodes count) :=
  WorkPermutation.hoareTime permutation (TermSpanLoop.machine 25) _ _ _
    (TermSpanLoop.hoareTime L count emitted R hR s hlen)

theorem formula_hoareTime (L count : ℕ) (emitted : List Bool) (R : Work → Prop)
    (hR : FormulaSpanLoop.Stable R) (s : FormulaSpanControl.State) (hlen : s.input.length ≤ L) :
    formulaMachine.HoareTime
      (fun inp work out => FormulaInv emitted R s inp work out ∧
        IsReg count (work (permutation (FormulaSpanLoop.fuel 24))))
      (fun inp work out => FormulaInv emitted R (FormulaSpanControl.run count s) inp work out ∧
        IsReg count (work (permutation (FormulaSpanLoop.fuel 24))))
      (FormulaSpanLoop.timeBound L s.terms s.formulas s.coordinates count) :=
  WorkPermutation.hoareTime permutation (FormulaSpanLoop.machine 24) _ _ _
    (FormulaSpanLoop.hoareTime L count emitted R hR s hlen)

theorem term_result {emitted : List Bool} {R : Work → Prop} {s : TermSpanControl.State}
    {inp out : Tape} {work : Work} (h : TermInv emitted R s inp work out) :
    Cursor s.before s.input emitted inp work out ∧ IsReg s.nodes (work (⟨13, by decide⟩ : Fin 32)) ∧
      (∀ j, Parked (work j)) ∧ (∀ j, (work j).cells 0 = Γ.start) := by
  refine ⟨physical_cursor h.1, h.2.nodeReg, ?_, ?_⟩
  · intro j
    simpa only [view, Equiv.apply_symm_apply] using h.2.safe (permutation.symm j)
  · intro j
    simpa only [view, Equiv.apply_symm_apply] using h.2.markers (permutation.symm j)

theorem formula_result {emitted : List Bool} {R : Work → Prop} {s : FormulaSpanControl.State}
    {inp out : Tape} {work : Work} (h : FormulaInv emitted R s inp work out) :
    Cursor s.before s.input emitted inp work out ∧ IsReg s.coordinates (work (⟨13, by decide⟩ : Fin 32)) ∧
      (∀ j, Parked (work j)) ∧ (∀ j, (work j).cells 0 = Γ.start) := by
  refine ⟨physical_cursor h.1, h.2.nodeReg, ?_, ?_⟩
  · intro j
    simpa only [view, Equiv.apply_symm_apply] using h.2.safe (permutation.symm j)
  · intro j
    simpa only [view, Equiv.apply_symm_apply] using h.2.markers (permutation.symm j)

end JointThermoComplexity.Complexity.RelocatedSpanQuery

#print axioms JointThermoComplexity.Complexity.RelocatedSpanQuery.term_hoareTime
#print axioms JointThermoComplexity.Complexity.RelocatedSpanQuery.formula_hoareTime
#print axioms JointThermoComplexity.Complexity.RelocatedSpanQuery.physical_frame
