module
public import proofs.JointThermoComplexity.Complexity.FormulaSpanCorrect

set_option autoImplicit false
@[expose] public section

/-! The formula-pending tape extends the checked term layout; every further tape remains outside. -/

namespace JointThermoComplexity.Complexity.FormulaSpanRegisters
open _root_.Complexity _root_.Complexity.TM
open HeaderAt (Cursor)
variable {n : ℕ}

def formulaPending (n : ℕ) : Fin (n + 8) := ⟨7, by omega⟩

theorem formulaPending_outside (n : ℕ) : TermSpanRegisters.Outside (n + 1) (formulaPending n) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; have := congrArg Fin.val h; change 7 = 3 at this; omega
  · intro h; have := congrArg Fin.val h; change 7 = 5 at this; omega
  · intro h; have := congrArg Fin.val h; change 7 = 6 at this; omega
  · intro i h; have := congrArg Fin.val h; change 7 = i.val at this; omega

theorem formulaPending_fuel (n : ℕ) : formulaPending n ≠ TermSpanRegisters.fuel (n + 1) := by
  intro h; have := congrArg Fin.val h; change 7 = 4 at this; omega

def Outside (n : ℕ) (j : Fin (n + 8)) : Prop := TermSpanRegisters.Outside (n + 1) j ∧ j ≠ formulaPending n
def Stable (R : (Fin (n + 8) → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, Outside n j → work' j = work j) → R work → R work'

def Frame (formulas : ℕ) (R : (Fin (n + 8) → Tape) → Prop) (work : Fin (n + 8) → Tape) : Prop :=
  IsReg formulas (work (formulaPending n)) ∧ R work

theorem frame_stable (formulas : ℕ) (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) :
    TermSpanRegisters.Stable (Frame formulas R) := by
  rintro work work' he ⟨hf, hr⟩
  exact ⟨by simpa only [he (formulaPending n) (formulaPending_outside n)] using hf,
    hR work work' (fun j hj => he j hj.1) hr⟩

def Inv (emitted : List Bool) (R : (Fin (n + 8) → Tape) → Prop) (s : FormulaSpanControl.State) :
    _root_.Complexity.TM.TapePred (n + 8) :=
  TermSpanRegisters.Inv emitted (Frame s.formulas R) (FormulaSpanControl.termState s)

theorem seq_inv_hoareTime (a b : TM (n + 8)) (emitted : List Bool) (R : (Fin (n + 8) → Tape) → Prop)
    (s u v : FormulaSpanControl.State) (ta tb : ℕ)
    (ha : a.HoareTime (Inv emitted R s) (Inv emitted R u) ta)
    (hb : b.HoareTime (Inv emitted R u) (Inv emitted R v) tb) :
    (seqTM a b).HoareTime (Inv emitted R s) (Inv emitted R v) (ta + 1 + tb) :=
  seqTM_hoareTime a b ha (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hb

theorem noop_hoareTime (emitted : List Bool) (R : (Fin (n + 8) → Tape) → Prop) (s : FormulaSpanControl.State) :
    (emitBitsTM (n := n + 8) []).HoareTime (Inv emitted R s) (Inv emitted R s) 0 :=
  TermSpanRegisters.noop_hoareTime emitted (Frame s.formulas R) (FormulaSpanControl.termState s)

theorem term_hoareTime (L v formulas coordinates : ℕ) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) :
    (TermSpanStep.machine (n + 1)).HoareTime (Inv emitted R ⟨before, input, v + 1, formulas, coordinates⟩)
      (Inv emitted R (FormulaSpanControl.step ⟨before, input, v + 1, formulas, coordinates⟩))
      (L + 2 * (v + 1) + 2 * coordinates + 42) :=
  TermSpanStep.hoareTime L emitted (Frame formulas R) (frame_stable formulas R hR)
    ⟨before, input, v + 1, coordinates⟩ hlen

def afterTag (s : FormulaSpanControl.State) : FormulaSpanControl.State :=
  ⟨s.before ++ s.input.take 3, s.input.drop 3, s.terms, s.formulas, s.coordinates⟩

theorem tag_hoareTime (emitted : List Bool) (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R)
    (s : FormulaSpanControl.State) :
    (TermSpanTagRead.machine (n + 1)).HoareTime (Inv emitted R s)
      (fun inp work out => Inv emitted R (afterTag s) inp work out ∧
        (work (TermSpanRegisters.flag (n + 1))).read = Γ.ofBool (SourceTags.accepted s.input) ∧
        SourceTagDispatch.Reads (List.ofFn (TermSpanRegisters.tags (n + 1))) (SourceTermToken.tagBits s.input) work) 8 :=
  TermSpanTagRead.hoareTime emitted (Frame s.formulas R) (frame_stable s.formulas R hR) (FormulaSpanControl.termState s)

end JointThermoComplexity.Complexity.FormulaSpanRegisters

#print axioms JointThermoComplexity.Complexity.FormulaSpanRegisters.frame_stable
#print axioms JointThermoComplexity.Complexity.FormulaSpanRegisters.term_hoareTime
#print axioms JointThermoComplexity.Complexity.FormulaSpanRegisters.tag_hoareTime
