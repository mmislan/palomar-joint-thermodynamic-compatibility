module
public import proofs.JointThermoComplexity.Complexity.MainNodeEquation
public import proofs.JointThermoComplexity.Complexity.PreorderEmissionControl

set_option autoImplicit false
@[expose] public section

/-! Actual unary pending tapes choose the local term/formula machine or the completed no-op. -/

namespace JointThermoComplexity.Complexity.PendingEquationDispatch
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryCounterInit MainEquationWork MainNodeEquation
open HeaderAt (Cursor)

def formulaMachine : TM 32 := FlagBranch.machine mainFormula (MainNodeEquation.machine false) (LeafLocalEquation.skip 0)
def machine : TM 32 := FlagBranch.machine mainTerm (MainNodeEquation.machine true) formulaMachine
noncomputable def timeBound (N : ℕ) : ℕ := MainNodeEquation.timeBound N + 4

theorem node_hoareTime (mode : Bool) (s : FormulaSpanControl.State) (arity L N : ℕ) (emitted : List Bool)
    (ha : arity ≤ N) (hL : L ≤ N) (hc : s.coordinates ≤ N) (hp : s.before.length ≤ N) (hlen : s.input.length ≤ L)
    (R : Work → Prop) (hR : Stable R) :
    (MainNodeEquation.machine mode).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Bounded s arity L N R work)
      (fun inp work out => Cursor s.before s.input
        (emitted ++ RowEntriesCodec.entries (EquationTagDispatch.rows mode L (root mode arity s) s.input)) inp work out ∧
          Bounded s arity L N R work) (MainNodeEquation.timeBound N) := by
  rintro inp work out ⟨hcur, adjusted, counts, values, hr, hadj, hq, hv, _⟩
  exact MainNodeEquation.hoareTime mode s arity L N adjusted counts values emitted ha hL hc hp hlen hadj hq hv R hR
    inp work out ⟨hcur, hr⟩

theorem term_read (s : FormulaSpanControl.State) (arity L N : ℕ) (R : Work → Prop) (work : Work)
    (hr : Bounded s arity L N R work) : (work mainTerm).read = if s.terms = 0 then Γ.blank else Γ.one := by
  obtain ⟨_, _, _, hb, _, _, _, _⟩ := hr
  exact hb.2.2.basic.frame.termReg.read_eq

theorem formula_read (s : FormulaSpanControl.State) (arity L N : ℕ) (R : Work → Prop) (work : Work)
    (hr : Bounded s arity L N R work) : (work mainFormula).read = if s.formulas = 0 then Γ.blank else Γ.one := by
  obtain ⟨_, _, _, hb, _, _, _, _⟩ := hr
  exact hb.2.2.basic.frame.formulaReg.read_eq

theorem noop_hoareTime (s : FormulaSpanControl.State) (arity L N : ℕ) (emitted : List Bool) (R : Work → Prop) :
    (LeafLocalEquation.skip 0).HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Bounded s arity L N R work)
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Bounded s arity L N R work) 0 := by
  simpa only [List.take_zero, List.drop_zero, List.append_nil, Nat.mul_zero] using
    LeafLocalEquation.skip_hoareTime 0 s.before s.input emitted (fun work _ => Bounded s arity L N R work)

theorem formula_hoareTime (forms coords arity L N : ℕ) (before input emitted : List Bool)
    (ha : arity ≤ N) (hL : L ≤ N) (hc : coords ≤ N) (hp : before.length ≤ N) (hlen : input.length ≤ L)
    (R : Work → Prop) (hR : Stable R) :
    formulaMachine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Bounded ⟨before, input, 0, forms, coords⟩ arity L N R work)
      (fun inp work out => Cursor before input
        (emitted ++ RowEntriesCodec.entries (PreorderEmissionControl.localRows L arity ⟨before, input, 0, forms, coords⟩)) inp work out ∧
          Bounded ⟨before, input, 0, forms, coords⟩ arity L N R work) (MainNodeEquation.timeBound N + 2) := by
  cases forms with
  | zero =>
    have hn := noop_hoareTime ⟨before, input, 0, 0, coords⟩ arity L N emitted R
    have hb := FlagBranchNonone.hoareTime mainFormula (MainNodeEquation.machine false) (LeafLocalEquation.skip 0)
      before input emitted before input emitted (Bounded ⟨before, input, 0, 0, coords⟩ arity L N R)
      (Bounded ⟨before, input, 0, 0, coords⟩ arity L N R) 0 hn
    apply hb.consequence
    · rintro inp work out ⟨hcur, hr⟩
      refine ⟨⟨hcur, hr⟩, ?_⟩
      have hv : (work mainFormula).read = Γ.blank := by
        simpa only [ite_true] using formula_read ⟨before, input, 0, 0, coords⟩ arity L N R work hr
      rw [hv]
      decide
    · intro inp work out hr
      simpa only [PreorderEmissionControl.localRows, RowEntriesCodec.entries, List.append_nil] using hr
    · omega
  | succ forms =>
    have hn := node_hoareTime false ⟨before, input, 0, forms + 1, coords⟩ arity L N emitted ha hL hc hp hlen R hR
    have hb := FlagBranchRun.yes_hoareTime mainFormula (MainNodeEquation.machine false) (LeafLocalEquation.skip 0)
      before input emitted before input
      (emitted ++ RowEntriesCodec.entries (EquationTagDispatch.rows false L (root false arity ⟨before, input, 0, forms + 1, coords⟩) input))
      (Bounded ⟨before, input, 0, forms + 1, coords⟩ arity L N R)
      (Bounded ⟨before, input, 0, forms + 1, coords⟩ arity L N R) (MainNodeEquation.timeBound N) hn
    apply hb.consequence
    · rintro inp work out ⟨hcur, hr⟩
      exact ⟨⟨hcur, hr⟩, by simpa only [Nat.add_one_ne_zero, ite_false] using formula_read ⟨before, input, 0, forms + 1, coords⟩ arity L N R work hr⟩
    · intro inp work out hr
      simpa only [PreorderEmissionControl.localRows, PreorderEmissionControl.address, EquationTagDispatch.rows,
        root, GeneratedNodeAddress.corrected, Bool.false_eq_true, ↓reduceIte] using hr
    · omega

theorem hoareTime (s : FormulaSpanControl.State) (arity L N : ℕ) (emitted : List Bool)
    (ha : arity ≤ N) (hL : L ≤ N) (hc : s.coordinates ≤ N) (hp : s.before.length ≤ N) (hlen : s.input.length ≤ L)
    (R : Work → Prop) (hR : Stable R) :
    machine.HoareTime
      (fun inp work out => Cursor s.before s.input emitted inp work out ∧ Bounded s arity L N R work)
      (fun inp work out => Cursor s.before s.input
        (emitted ++ RowEntriesCodec.entries (PreorderEmissionControl.localRows L arity s)) inp work out ∧ Bounded s arity L N R work)
      (timeBound N) := by
  cases s with
  | mk before input terms forms coords =>
    cases terms with
    | zero =>
      have hf := formula_hoareTime forms coords arity L N before input emitted ha hL hc hp hlen R hR
      have hb := FlagBranchNonone.hoareTime mainTerm (MainNodeEquation.machine true) formulaMachine before input emitted before input
        (emitted ++ RowEntriesCodec.entries (PreorderEmissionControl.localRows L arity ⟨before, input, 0, forms, coords⟩))
        (Bounded ⟨before, input, 0, forms, coords⟩ arity L N R) (Bounded ⟨before, input, 0, forms, coords⟩ arity L N R)
        (MainNodeEquation.timeBound N + 2) hf
      apply hb.consequence
      · rintro inp work out ⟨hcur, hr⟩
        refine ⟨⟨hcur, hr⟩, ?_⟩
        have hv : (work mainTerm).read = Γ.blank := by
          simpa only [ite_true] using term_read ⟨before, input, 0, forms, coords⟩ arity L N R work hr
        rw [hv]
        decide
      · exact fun _ _ _ hr => hr
      · dsimp [timeBound]
        omega
    | succ terms =>
      have hn := node_hoareTime true ⟨before, input, terms + 1, forms, coords⟩ arity L N emitted ha hL hc hp hlen R hR
      have hb := FlagBranchRun.yes_hoareTime mainTerm (MainNodeEquation.machine true) formulaMachine before input emitted before input
        (emitted ++ RowEntriesCodec.entries (EquationTagDispatch.rows true L (root true arity ⟨before, input, terms + 1, forms, coords⟩) input))
        (Bounded ⟨before, input, terms + 1, forms, coords⟩ arity L N R) (Bounded ⟨before, input, terms + 1, forms, coords⟩ arity L N R)
        (MainNodeEquation.timeBound N) hn
      apply hb.consequence
      · rintro inp work out ⟨hcur, hr⟩
        exact ⟨⟨hcur, hr⟩, by simpa only [Nat.add_one_ne_zero, ite_false] using term_read ⟨before, input, terms + 1, forms, coords⟩ arity L N R work hr⟩
      · intro inp work out hr
        simpa only [PreorderEmissionControl.localRows, PreorderEmissionControl.address, EquationTagDispatch.rows,
          root, GeneratedNodeAddress.corrected, ↓reduceIte] using hr
      · dsimp [timeBound]
        omega

end JointThermoComplexity.Complexity.PendingEquationDispatch

#print axioms JointThermoComplexity.Complexity.PendingEquationDispatch.hoareTime
