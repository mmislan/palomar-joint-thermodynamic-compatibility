module
public import proofs.JointThermoComplexity.Complexity.FormulaSpanBody

set_option autoImplicit false
@[expose] public section

/-! Actual total mixed traversal step, with independent term/formula pending guards and exact allocation. -/

namespace JointThermoComplexity.Complexity.FormulaSpanStep
open _root_.Complexity _root_.Complexity.TM FormulaSpanRegisters
open HeaderAt (Cursor)
variable {n : ℕ}

def presenceMachine (n : ℕ) : TM (n + 8) := FlagBranch.machine (TermSpanRegisters.flag (n + 1))
  (FormulaSpanBody.machine n) (FormulaSpanBody.simpleMachine n false)
def formulaTokenMachine (n : ℕ) : TM (n + 8) := seqTM (TermSpanTagRead.machine (n + 1)) (presenceMachine n)
def zeroTermMachine (n : ℕ) : TM (n + 8) := FlagBranch.machine (formulaPending n) (formulaTokenMachine n) (emitBitsTM [])
def machine (n : ℕ) : TM (n + 8) := FlagBranch.machine (TermSpanRegisters.pending (n + 1))
  (TermSpanStep.machine (n + 1)) (zeroTermMachine n)

theorem after_true (v coordinates : ℕ) (before input : List Bool) (ht : SourceTags.accepted input = true) :
    FormulaSpanBody.after (SourceTermToken.tagBits input) v coordinates (before ++ input.take 3) (input.drop 3) =
      FormulaSpanControl.formulaStep v ⟨before, input, 0, v + 1, coordinates⟩ := by
  simp only [FormulaSpanBody.after, FormulaSpanControl.formulaStep, ht, ↓reduceIte]

theorem after_false (v coordinates : ℕ) (before input : List Bool) (ht : SourceTags.accepted input = false) :
    (⟨before ++ input.take 3, input.drop 3, 0, v, coordinates + 1⟩ : FormulaSpanControl.State) =
      FormulaSpanControl.formulaStep v ⟨before, input, 0, v + 1, coordinates⟩ := by
  simp only [FormulaSpanControl.formulaStep, ht, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem presence_hoareTime (v coordinates : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) :
    (presenceMachine n).HoareTime
      (fun inp work out => Inv emitted R (afterTag ⟨before, input, 0, v + 1, coordinates⟩) inp work out ∧
        (work (TermSpanRegisters.flag (n + 1))).read = Γ.ofBool (SourceTags.accepted input) ∧
        SourceTagDispatch.Reads (List.ofFn (TermSpanRegisters.tags (n + 1))) (SourceTermToken.tagBits input) work)
      (Inv emitted R (FormulaSpanControl.formulaStep v ⟨before, input, 0, v + 1, coordinates⟩)) (2 * v + 8 * coordinates + 82) := by
  cases ht : SourceTags.accepted input with
  | false =>
    have hn := FormulaSpanBody.simple_hoareTime false v coordinates (before ++ input.take 3) (input.drop 3) emitted R hR
    have hb := FlagBranchRun.no_hoareTime (TermSpanRegisters.flag (n + 1)) (FormulaSpanBody.machine n)
      (FormulaSpanBody.simpleMachine n false) (before ++ input.take 3) (input.drop 3) emitted
      (before ++ input.take 3) (input.drop 3) emitted
      (TermSpanRegisters.Ready 0 coordinates (Frame (v + 1) R))
      (TermSpanRegisters.Ready 0 (coordinates + 1) (Frame v R)) (2 * v + 2 * coordinates + 19) hn
    exact hb.consequence (by
      rintro inp work out ⟨hp, hf, _hreads⟩
      exact ⟨hp, by simpa only [ht, Γ.ofBool] using hf⟩) (by
      intro inp work out hp
      change Inv emitted R ⟨before ++ input.take 3, input.drop 3, 0, v, coordinates + 1⟩ inp work out at hp
      rw [after_false v coordinates before input ht] at hp
      exact hp) (by omega)
  | true =>
    let next := FormulaSpanBody.after (SourceTermToken.tagBits input) v coordinates (before ++ input.take 3) (input.drop 3)
    let P : (Fin (n + 8) → Tape) → Prop := fun work =>
      TermSpanRegisters.Ready 0 coordinates (Frame (v + 1) R) work ∧
        SourceTagDispatch.Reads (List.ofFn (TermSpanRegisters.tags (n + 1))) (SourceTermToken.tagBits input) work
    have hm := FormulaSpanBody.hoareTime (SourceTermToken.tagBits input) (by simp [SourceTermToken.tagBits])
      v coordinates (before ++ input.take 3) (input.drop 3) emitted R hR
    have hb := FlagBranchRun.yes_hoareTime (TermSpanRegisters.flag (n + 1)) (FormulaSpanBody.machine n)
      (FormulaSpanBody.simpleMachine n false) (before ++ input.take 3) (input.drop 3) emitted next.before next.input emitted
      P (TermSpanRegisters.Ready next.terms next.coordinates (Frame next.formulas R)) (2 * v + 8 * coordinates + 80)
      (hm.consequence (by rintro inp work out ⟨hc, hr, hreads⟩; exact ⟨⟨hc, hr⟩, hreads⟩) (fun _ _ _ h => h) le_rfl)
    exact hb.consequence (by
      rintro inp work out ⟨⟨hc, hr⟩, hf, hreads⟩
      exact ⟨⟨hc, hr, hreads⟩, by simpa only [ht, Γ.ofBool] using hf⟩) (by
      intro inp work out hp
      change Inv emitted R next inp work out at hp
      have he : next = FormulaSpanControl.formulaStep v ⟨before, input, 0, v + 1, coordinates⟩ := after_true v coordinates before input ht
      rw [he] at hp
      exact hp) (by omega)

theorem formulaToken_hoareTime (v coordinates : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) :
    (formulaTokenMachine n).HoareTime (Inv emitted R ⟨before, input, 0, v + 1, coordinates⟩)
      (Inv emitted R (FormulaSpanControl.formulaStep v ⟨before, input, 0, v + 1, coordinates⟩)) (2 * v + 8 * coordinates + 91) := by
  have ht := tag_hoareTime emitted R hR ⟨before, input, 0, v + 1, coordinates⟩
  have hp := presence_hoareTime v coordinates before input emitted R hR
  have h := seqTM_hoareTime (TermSpanTagRead.machine (n + 1)) (presenceMachine n) ht (by
    rintro inp work out ⟨⟨hc, hr⟩, hf, hreads⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, hr⟩, hf, hreads⟩) hp
  exact h.mono_bound (by omega)

theorem zeroTerm_hoareTime (formulas coordinates : ℕ) (before input emitted : List Bool)
    (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R) :
    (zeroTermMachine n).HoareTime (Inv emitted R ⟨before, input, 0, formulas, coordinates⟩)
      (Inv emitted R (FormulaSpanControl.step ⟨before, input, 0, formulas, coordinates⟩)) (2 * formulas + 8 * coordinates + 94) := by
  cases formulas with
  | zero =>
    have hn := noop_hoareTime emitted R (⟨before, input, 0, 0, coordinates⟩ : FormulaSpanControl.State)
    have hb := FlagBranchNonone.hoareTime (formulaPending n) (formulaTokenMachine n) (emitBitsTM [])
      before input emitted before input emitted (TermSpanRegisters.Ready 0 coordinates (Frame 0 R))
      (TermSpanRegisters.Ready 0 coordinates (Frame 0 R)) 0 hn
    exact hb.consequence (by
      rintro inp work out ⟨hc, hr⟩
      refine ⟨⟨hc, hr⟩, ?_⟩
      have hv := hr.frame.1.read_eq
      change (work (formulaPending n)).read = Γ.blank at hv
      rw [hv]; decide) (fun _ _ _ h => h) (by omega)
  | succ v =>
    let next := FormulaSpanControl.formulaStep v ⟨before, input, 0, v + 1, coordinates⟩
    have hm := formulaToken_hoareTime v coordinates before input emitted R hR
    have hb := FlagBranchRun.yes_hoareTime (formulaPending n) (formulaTokenMachine n) (emitBitsTM [])
      before input emitted next.before next.input emitted (TermSpanRegisters.Ready 0 coordinates (Frame (v + 1) R))
      (TermSpanRegisters.Ready next.terms next.coordinates (Frame next.formulas R)) (2 * v + 8 * coordinates + 91) hm
    exact hb.consequence (by
      rintro inp work out ⟨hc, hr⟩
      refine ⟨⟨hc, hr⟩, ?_⟩
      have hv := hr.frame.1.read_eq
      simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using hv)
      (fun _ _ _ h => h) (by omega)

theorem hoareTime (L : ℕ) (emitted : List Bool) (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R)
    (s : FormulaSpanControl.State) (hlen : s.input.length ≤ L) :
    (machine n).HoareTime (Inv emitted R s) (Inv emitted R (FormulaSpanControl.step s))
      (L + 2 * s.terms + 2 * s.formulas + 8 * s.coordinates + 100) := by
  rcases s with ⟨before, input, terms, formulas, coordinates⟩
  cases terms with
  | zero =>
    let next := FormulaSpanControl.step ⟨before, input, 0, formulas, coordinates⟩
    have hm := zeroTerm_hoareTime formulas coordinates before input emitted R hR
    have hb := FlagBranchNonone.hoareTime (TermSpanRegisters.pending (n + 1)) (TermSpanStep.machine (n + 1)) (zeroTermMachine n)
      before input emitted next.before next.input emitted (TermSpanRegisters.Ready 0 coordinates (Frame formulas R))
      (TermSpanRegisters.Ready next.terms next.coordinates (Frame next.formulas R)) (2 * formulas + 8 * coordinates + 94) hm
    exact hb.consequence (by
      rintro inp work out ⟨hc, hr⟩
      refine ⟨⟨hc, hr⟩, ?_⟩
      have hv := hr.counter.read_eq
      change (work (TermSpanRegisters.pending (n + 1))).read = Γ.blank at hv
      rw [hv]; decide) (fun _ _ _ h => h) (by
        change 2 * formulas + 8 * coordinates + 94 + 2 ≤ L + 2 * 0 + 2 * formulas + 8 * coordinates + 100
        omega)
  | succ v =>
    let next := FormulaSpanControl.step ⟨before, input, v + 1, formulas, coordinates⟩
    have hm := term_hoareTime L v formulas coordinates before input emitted hlen R hR
    have hb := FlagBranchRun.yes_hoareTime (TermSpanRegisters.pending (n + 1)) (TermSpanStep.machine (n + 1)) (zeroTermMachine n)
      before input emitted next.before next.input emitted (TermSpanRegisters.Ready (v + 1) coordinates (Frame formulas R))
      (TermSpanRegisters.Ready next.terms next.coordinates (Frame next.formulas R)) (L + 2 * (v + 1) + 2 * coordinates + 42) hm
    exact hb.consequence (by
      rintro inp work out ⟨hc, hr⟩
      refine ⟨⟨hc, hr⟩, ?_⟩
      have hv := hr.counter.read_eq
      change (work (TermSpanRegisters.pending (n + 1))).read = (if v + 1 = 0 then Γ.blank else Γ.one) at hv
      simpa only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using hv)
      (fun _ _ _ h => h) (by
        change L + 2 * (v + 1) + 2 * coordinates + 42 + 1 ≤ L + 2 * (v + 1) + 2 * formulas + 8 * coordinates + 100
        omega)

theorem bounded_hoareTime (L T F C : ℕ) (emitted : List Bool) (R : (Fin (n + 8) → Tape) → Prop) (hR : Stable R)
    (s : FormulaSpanControl.State) (hlen : s.input.length ≤ L) (ht : s.terms ≤ T) (hf : s.formulas ≤ F) (hc : s.coordinates ≤ C) :
    (machine n).HoareTime (Inv emitted R s) (Inv emitted R (FormulaSpanControl.step s)) (L + 2 * T + 2 * F + 8 * C + 100) :=
  (hoareTime L emitted R hR s hlen).mono_bound (by omega)

end JointThermoComplexity.Complexity.FormulaSpanStep

#print axioms JointThermoComplexity.Complexity.FormulaSpanStep.hoareTime
#print axioms JointThermoComplexity.Complexity.FormulaSpanStep.bounded_hoareTime
