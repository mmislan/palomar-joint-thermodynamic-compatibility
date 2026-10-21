module
public import proofs.JointThermoComplexity.Complexity.PhysicalSpanQuery
public import proofs.JointThermoComplexity.Complexity.InputCheckpointTransition

set_option autoImplicit false
@[expose] public section

/-! Total lookahead returns the exact size register and the original input cursor. -/

namespace JointThermoComplexity.Complexity.RestoredSpanQuery
open _root_.Complexity _root_.Complexity.TM HeaderAt RelocatedSpanQuery QueryWorkFrame PhysicalSpanQuery

def termMachine : TM 32 := InputCheckpoint.around position RelocatedSpanQuery.termMachine
def formulaMachine : TM 32 := InputCheckpoint.around position RelocatedSpanQuery.formulaMachine

def termTime (L p : ℕ) : ℕ := 5 * L ^ 2 + 48 * L + 13 * p + 25
def formulaTime (L p : ℕ) : ℕ := 39 * L ^ 2 + 106 * L + 13 * p + 25

theorem term_hoareTime (L : ℕ) (before input emitted : List Bool) (R : Work → Prop)
    (hR : Stable R) (hlen : input.length ≤ L) :
    termMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work position) ∧ Ready 1 0 0 L R work)
      (fun inp work out =>
        let q := PreorderLookahead.termResult L input
        Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg 0 (work position) ∧ Ready q.pending 0 q.nodes L R work)
      (termTime L before.length) := by
  let q := PreorderLookahead.termResult L input
  have hsplit : (before ++ q.before) ++ q.input = before ++ input := by
    have hw := (TermSpanControl.run_bounds L ⟨[], input, 1, 0⟩).2.2.2
    change q.before ++ q.input = input at hw
    rw [List.append_assoc, hw]
  have hq := PhysicalSpanQuery.term_hoareTime L L before.length 1 0 0 before input emitted R hR hlen
  rw [term_result_prefix] at hq
  have h := InputCheckpointTransition.hoareTime position RelocatedSpanQuery.termMachine before input
    (before ++ q.before) q.input emitted emitted hsplit (Ready 1 0 0 L R) (Ready q.pending 0 q.nodes L R)
    (ready_position 1 0 0 L R hR) (ready_position q.pending 0 q.nodes L R hR)
    (TermSpanLoop.timeBound L 1 0 L) hq
  apply HoareTime.mono_bound h
  have hw := congrArg List.length (TermSpanControl.run_bounds L ⟨[], input, 1, 0⟩).2.2.2
  change (q.before ++ q.input).length = input.length at hw
  simp only [List.length_append] at hw ⊢
  rw [TermSpanLoop.quadratic_timeBound]
  unfold termTime
  omega

theorem formula_hoareTime (L : ℕ) (before input emitted : List Bool) (R : Work → Prop)
    (hR : Stable R) (hlen : input.length ≤ L) :
    formulaMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work position) ∧ Ready 0 1 0 L R work)
      (fun inp work out =>
        let q := PreorderLookahead.formulaResult L input
        Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg 0 (work position) ∧ Ready q.terms q.formulas q.coordinates L R work)
      (formulaTime L before.length) := by
  let q := PreorderLookahead.formulaResult L input
  have hsplit : (before ++ q.before) ++ q.input = before ++ input := by
    have hw := (FormulaSpanControl.run_bounds L ⟨[], input, 0, 1, 0⟩).2.2.2.2
    change q.before ++ q.input = input at hw
    rw [List.append_assoc, hw]
  have hq := PhysicalSpanQuery.formula_hoareTime L L before.length 0 1 0 before input emitted R hR hlen
  rw [formula_result_prefix] at hq
  have h := InputCheckpointTransition.hoareTime position RelocatedSpanQuery.formulaMachine before input
    (before ++ q.before) q.input emitted emitted hsplit (Ready 0 1 0 L R)
    (Ready q.terms q.formulas q.coordinates L R)
    (ready_position 0 1 0 L R hR) (ready_position q.terms q.formulas q.coordinates L R hR)
    (FormulaSpanLoop.timeBound L 0 1 0 L) hq
  apply HoareTime.mono_bound h
  have hw := congrArg List.length (FormulaSpanControl.run_bounds L ⟨[], input, 0, 1, 0⟩).2.2.2.2
  change (q.before ++ q.input).length = input.length at hw
  simp only [List.length_append] at hw ⊢
  rw [FormulaSpanLoop.quadratic_timeBound]
  unfold formulaTime
  omega

end JointThermoComplexity.Complexity.RestoredSpanQuery

#print axioms JointThermoComplexity.Complexity.RestoredSpanQuery.term_hoareTime
#print axioms JointThermoComplexity.Complexity.RestoredSpanQuery.formula_hoareTime
