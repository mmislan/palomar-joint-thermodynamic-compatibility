module
public import proofs.JointThermoComplexity.Complexity.QueryWorkFrame

set_option autoImplicit false
@[expose] public section

/-! Transfer physical query registers to the existing actual traversal invariants. -/

namespace JointThermoComplexity.Complexity.QueryInvariantTransfer
open _root_.Complexity _root_.Complexity.TM HeaderAt EquationQueryLayout RelocatedSpanQuery QueryWorkFrame

theorem cursor_view {before input emitted : List Bool} {inp out : Tape} {work : Work}
    (hc : Cursor before input emitted inp work out) : Cursor before input emitted inp (view work) out :=
  ⟨hc.cells, hc.head, fun j => hc.works (permutation j), hc.tapePrefix, hc.zero⟩

theorem markers {tp fp nodes budget p : ℕ} {R : Work → Prop} {work : Work}
    (hr : Ready tp fp nodes budget R work) (hp : IsReg p (work position)) :
    ∀ j, (view work j).cells 0 = Γ.start := by
  intro j
  by_cases hj : permutation j = position
  · simpa only [view, hj] using hp.cell0
  · exact hr.markers (permutation j) hj

theorem term_input (tp fp nodes budget p : ℕ) (before input emitted : List Bool) (R : Work → Prop)
    (inp out : Tape) (work : Work) (hc : Cursor before input emitted inp work out)
    (hs : ∀ j, Parked (work j)) (hp : IsReg p (work position)) (hr : Ready tp fp nodes budget R work) :
    TermInv emitted (TermExtra p fp R) ⟨before, input, tp, nodes⟩ inp work out ∧
      IsReg budget (work (permutation (TermSpanRegisters.fuel 25))) := by
  refine ⟨⟨cursor_view hc, ?_⟩, hr.fuelReg⟩
  refine ⟨fun j => hs (permutation j), markers hr hp, hr.termReg, hr.nodeReg, ?_, hr.flagHead, ?_⟩
  · intro i
    simpa only [view, term_tags] using hr.tagHeads i
  · simpa only [TermExtra, unview_view] using
      (show IsReg p (work position) ∧ IsReg fp (work formulas) ∧ R work from ⟨hp, hr.formulaReg, hr.frame⟩)

theorem formula_input (tp fp nodes budget p : ℕ) (before input emitted : List Bool) (R : Work → Prop)
    (inp out : Tape) (work : Work) (hc : Cursor before input emitted inp work out)
    (hs : ∀ j, Parked (work j)) (hp : IsReg p (work position)) (hr : Ready tp fp nodes budget R work) :
    FormulaInv emitted (FormulaExtra p R) ⟨before, input, tp, fp, nodes⟩ inp work out ∧
      IsReg budget (work (permutation (FormulaSpanLoop.fuel 24))) := by
  refine ⟨⟨cursor_view hc, ?_⟩, hr.fuelReg⟩
  refine ⟨fun j => hs (permutation j), markers hr hp, hr.termReg, hr.nodeReg, ?_, hr.flagHead, hr.formulaReg, ?_⟩
  · intro i
    simpa only [view, Nat.reduceAdd, term_tags] using hr.tagHeads i
  · simpa only [FormulaExtra, unview_view] using (show IsReg p (work position) ∧ R work from ⟨hp, hr.frame⟩)

theorem term_output (fp budget p : ℕ) (emitted : List Bool) (R : Work → Prop) (s : TermSpanControl.State)
    (inp out : Tape) (work : Work) (h : TermInv emitted (TermExtra p fp R) s inp work out)
    (hf : IsReg budget (work (permutation (TermSpanRegisters.fuel 25)))) :
    Cursor s.before s.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg p (work position) ∧
      Ready s.pending fp s.nodes budget R work := by
  obtain ⟨hc, hn, hs, hz⟩ := term_result h
  have he : IsReg p (work position) ∧ IsReg fp (work formulas) ∧ R work := by
    simpa only [TermExtra, unview_view] using h.2.frame
  refine ⟨hc, hs, he.1, fun j _ => hz j, ?_, h.2.flagHead, h.2.counter, he.2.1, hn, hf, he.2.2⟩
  intro i
  simpa only [view, term_tags] using h.2.tagHeads i

theorem formula_output (budget p : ℕ) (emitted : List Bool) (R : Work → Prop) (s : FormulaSpanControl.State)
    (inp out : Tape) (work : Work) (h : FormulaInv emitted (FormulaExtra p R) s inp work out)
    (hf : IsReg budget (work (permutation (FormulaSpanLoop.fuel 24)))) :
    Cursor s.before s.input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg p (work position) ∧
      Ready s.terms s.formulas s.coordinates budget R work := by
  obtain ⟨hc, hn, hs, hz⟩ := formula_result h
  have he : IsReg p (work position) ∧ R work := by
    simpa only [FormulaExtra, unview_view] using h.2.frame.2
  refine ⟨hc, hs, he.1, fun j _ => hz j, ?_, h.2.flagHead, h.2.counter, h.2.frame.1, hn, hf, he.2⟩
  intro i
  simpa only [view, Nat.reduceAdd, term_tags] using h.2.tagHeads i

end JointThermoComplexity.Complexity.QueryInvariantTransfer

#print axioms JointThermoComplexity.Complexity.QueryInvariantTransfer.term_input
#print axioms JointThermoComplexity.Complexity.QueryInvariantTransfer.formula_output
