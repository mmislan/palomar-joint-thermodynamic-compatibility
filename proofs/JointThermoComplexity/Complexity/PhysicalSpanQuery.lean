module
public import proofs.JointThermoComplexity.Complexity.QueryInvariantTransfer
public import proofs.JointThermoComplexity.Complexity.PreorderLookahead

set_option autoImplicit false
@[expose] public section

/-! Exact raw subtree traversal contracts in physical query registers. -/

namespace JointThermoComplexity.Complexity.PhysicalSpanQuery
open _root_.Complexity _root_.Complexity.TM HeaderAt RelocatedSpanQuery QueryWorkFrame QueryInvariantTransfer

theorem term_hoareTime (L count p tp fp nodes : ℕ) (before input emitted : List Bool)
    (R : Work → Prop) (hR : Stable R) (hlen : input.length ≤ L) :
    termMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ Ready tp fp nodes count R work)
      (fun inp work out =>
        let q := TermSpanControl.run count ⟨before, input, tp, nodes⟩
        Cursor q.before q.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg p (work position) ∧ Ready q.pending fp q.nodes count R work)
      (TermSpanLoop.timeBound L tp nodes count) := by
  rintro inp work out ⟨hc, hs, hp, hr⟩
  have hpre := term_input tp fp nodes count p before input emitted R inp out work hc hs hp hr
  obtain ⟨d, t, ht, hd, hh, hpost, hf⟩ :=
    RelocatedSpanQuery.term_hoareTime L count emitted (TermExtra p fp R) (term_extra_stable p fp R hR)
      ⟨before, input, tp, nodes⟩ hlen inp work out hpre
  exact ⟨d, t, ht, hd, hh, term_output fp count p emitted R _ d.input d.output d.work hpost hf⟩

theorem formula_hoareTime (L count p tp fp nodes : ℕ) (before input emitted : List Bool)
    (R : Work → Prop) (hR : Stable R) (hlen : input.length ≤ L) :
    formulaMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work position) ∧ Ready tp fp nodes count R work)
      (fun inp work out =>
        let q := FormulaSpanControl.run count ⟨before, input, tp, fp, nodes⟩
        Cursor q.before q.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
          IsReg p (work position) ∧ Ready q.terms q.formulas q.coordinates count R work)
      (FormulaSpanLoop.timeBound L tp fp nodes count) := by
  rintro inp work out ⟨hc, hs, hp, hr⟩
  have hpre := formula_input tp fp nodes count p before input emitted R inp out work hc hs hp hr
  obtain ⟨d, t, ht, hd, hh, hpost, hf⟩ :=
    RelocatedSpanQuery.formula_hoareTime L count emitted (FormulaExtra p R) (formula_extra_stable p R hR)
      ⟨before, input, tp, fp, nodes⟩ hlen inp work out hpre
  exact ⟨d, t, ht, hd, hh, formula_output count p emitted R _ d.input d.output d.work hpost hf⟩

def termPrefix (before : List Bool) (s : TermSpanControl.State) : TermSpanControl.State :=
  {s with before := before ++ s.before}

def formulaPrefix (before : List Bool) (s : FormulaSpanControl.State) : FormulaSpanControl.State :=
  {s with before := before ++ s.before}

theorem term_step_prefix (before : List Bool) (s : TermSpanControl.State) :
    TermSpanControl.step (termPrefix before s) = termPrefix before (TermSpanControl.step s) := by
  rcases s with ⟨seen, input, tp, nodes⟩
  cases tp <;> simp only [termPrefix, TermSpanControl.step, List.append_assoc]

theorem formula_step_prefix (before : List Bool) (s : FormulaSpanControl.State) :
    FormulaSpanControl.step (formulaPrefix before s) = formulaPrefix before (FormulaSpanControl.step s) := by
  rcases s with ⟨seen, input, tp, fp, nodes⟩
  cases tp with
  | zero =>
    cases fp with
    | zero => rfl
    | succ fp =>
      simp only [formulaPrefix, FormulaSpanControl.step, FormulaSpanControl.formulaStep, List.append_assoc]
      rfl
  | succ tp => simp only [formulaPrefix, FormulaSpanControl.step, FormulaSpanControl.fromTerm,
      FormulaSpanControl.termState, TermSpanControl.step, List.append_assoc]

theorem term_run_prefix (count : ℕ) (before : List Bool) (s : TermSpanControl.State) :
    TermSpanControl.run count (termPrefix before s) = termPrefix before (TermSpanControl.run count s) := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih =>
    change TermSpanControl.run count (TermSpanControl.step (termPrefix before s)) = _
    rw [term_step_prefix, ih]
    rfl

theorem formula_run_prefix (count : ℕ) (before : List Bool) (s : FormulaSpanControl.State) :
    FormulaSpanControl.run count (formulaPrefix before s) = formulaPrefix before (FormulaSpanControl.run count s) := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih =>
    change FormulaSpanControl.run count (FormulaSpanControl.step (formulaPrefix before s)) = _
    rw [formula_step_prefix, ih]
    rfl

theorem term_result_prefix (L : ℕ) (before input : List Bool) :
    TermSpanControl.run L ⟨before, input, 1, 0⟩ = termPrefix before (PreorderLookahead.termResult L input) := by
  simpa only [termPrefix, PreorderLookahead.termResult, List.append_nil] using term_run_prefix L before ⟨[], input, 1, 0⟩

theorem formula_result_prefix (L : ℕ) (before input : List Bool) :
    FormulaSpanControl.run L ⟨before, input, 0, 1, 0⟩ = formulaPrefix before (PreorderLookahead.formulaResult L input) := by
  simpa only [formulaPrefix, PreorderLookahead.formulaResult, List.append_nil] using formula_run_prefix L before ⟨[], input, 0, 1, 0⟩

end JointThermoComplexity.Complexity.PhysicalSpanQuery

#print axioms JointThermoComplexity.Complexity.PhysicalSpanQuery.term_hoareTime
#print axioms JointThermoComplexity.Complexity.PhysicalSpanQuery.formula_result_prefix
