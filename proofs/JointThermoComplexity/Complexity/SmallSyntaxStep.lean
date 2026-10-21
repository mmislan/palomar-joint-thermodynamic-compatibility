module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxDispatch

set_option autoImplicit false
@[expose] public section

/-! One actual total syntax-stream token, including truncated-tag presence and both parse modes. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxStep
open _root_.Complexity _root_.Complexity.TM SmallSyntaxRegisters SmallSyntaxTermBody
open HeaderAt (Cursor)

def presenceMachine : TM 6 := FlagBranch.machine flag SmallSyntaxDispatch.machine (emitBitsTM [])
def machine : TM 6 := seqTM SmallSyntaxTagRead.machine presenceMachine

theorem after_true (s : SmallSyntaxControl.State) (htag : SourceTags.accepted s.input = true) :
    after (SmallSyntaxTagRead.afterTag s) (SmallSyntaxToken.body s.pending (SourceTermToken.tagBits s.input) (s.input.drop 3)) =
      SmallSyntaxControl.step s := by
  simp only [after, SmallSyntaxTagRead.afterTag, SmallSyntaxControl.step, SmallSyntaxToken.step, htag, ↓reduceIte, List.append_assoc]

theorem after_false (s : SmallSyntaxControl.State) (htag : SourceTags.accepted s.input = false) :
    SmallSyntaxTagRead.afterTag s = SmallSyntaxControl.step s := by
  simp only [SmallSyntaxTagRead.afterTag, SmallSyntaxControl.step, SmallSyntaxToken.step, htag, Bool.false_eq_true,
    ↓reduceIte, List.append_nil]

theorem presence_hoareTime (L : ℕ) (R : (Fin 6 → Tape) → Prop) (hR : Stable R)
    (s : SmallSyntaxControl.State) (hlen : s.input.length ≤ L) :
    presenceMachine.HoareTime
      (fun inp work out => Inv R (SmallSyntaxTagRead.afterTag s) inp work out ∧
        (work flag).read = Γ.ofBool (SourceTags.accepted s.input) ∧
        SourceTagDispatch.Reads (List.ofFn tags) (SourceTermToken.tagBits s.input) work)
      (Inv R (SmallSyntaxControl.step s)) (12 * L + 2 * s.pending + 36) := by
  cases htag : SourceTags.accepted s.input with
  | false =>
    have hn := emit_hoareTime [] R (SmallSyntaxTagRead.afterTag s)
    have hn' : (emitBitsTM (n := 6) []).HoareTime (Inv R (SmallSyntaxTagRead.afterTag s))
        (Inv R (SmallSyntaxTagRead.afterTag s)) 0 := by
      simpa only [SmallSyntaxTagRead.afterTag, List.append_nil, List.length_nil] using hn
    have hb := FlagBranchRun.no_hoareTime flag SmallSyntaxDispatch.machine (emitBitsTM [])
      (SmallSyntaxTagRead.afterTag s).before (SmallSyntaxTagRead.afterTag s).input s.emitted
      (SmallSyntaxTagRead.afterTag s).before (SmallSyntaxTagRead.afterTag s).input s.emitted
      (Ready s.pending R) (Ready s.pending R) 0 hn'
    exact hb.consequence (by
      rintro inp work out ⟨hp, hf, _ht⟩
      exact ⟨hp, by simpa only [htag, Γ.ofBool] using hf⟩) (by
      intro inp work out hp
      change Inv R (SmallSyntaxTagRead.afterTag s) inp work out at hp
      rw [after_false s htag] at hp
      exact hp) (by omega)
  | true =>
    let next := after (SmallSyntaxTagRead.afterTag s)
      (SmallSyntaxToken.body s.pending (SourceTermToken.tagBits s.input) (s.input.drop 3))
    let P : (Fin 6 → Tape) → Prop := fun work => Ready s.pending R work ∧
      SourceTagDispatch.Reads (List.ofFn tags) (SourceTermToken.tagBits s.input) work
    have hdrop : (s.input.drop 3).length ≤ L := by rw [List.length_drop]; omega
    have hm := SmallSyntaxDispatch.hoareTime (SourceTermToken.tagBits s.input) (by simp [SourceTermToken.tagBits])
      L s.pending (SmallSyntaxTagRead.afterTag s).before (s.input.drop 3) s.emitted hdrop R hR
    have hb := FlagBranchRun.yes_hoareTime flag SmallSyntaxDispatch.machine (emitBitsTM [])
      (SmallSyntaxTagRead.afterTag s).before (s.input.drop 3) s.emitted next.before next.input next.emitted
      P (Ready next.pending R) (12 * L + 2 * s.pending + 34) hm
    exact hb.consequence (by
      rintro inp work out ⟨⟨hc, hr⟩, hf, ht⟩
      exact ⟨⟨hc, hr, ht⟩, by simpa only [htag, Γ.ofBool] using hf⟩) (by
      intro inp work out hp
      change Inv R next inp work out at hp
      have he : next = SmallSyntaxControl.step s := after_true s htag
      rw [he] at hp
      exact hp) (by omega)

theorem hoareTime (L : ℕ) (R : (Fin 6 → Tape) → Prop) (hR : Stable R)
    (s : SmallSyntaxControl.State) (hlen : s.input.length ≤ L) :
    machine.HoareTime (Inv R s) (Inv R (SmallSyntaxControl.step s)) (12 * L + 2 * s.pending + 50) := by
  have ht := SmallSyntaxTagRead.hoareTime R hR s
  have hp := presence_hoareTime L R hR s hlen
  have h := seqTM_hoareTime SmallSyntaxTagRead.machine presenceMachine ht (by
    rintro inp work out ⟨⟨hc, hr⟩, hf, hv⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, hr⟩, hf, hv⟩) hp
  exact h.mono_bound (by omega)

theorem bounded_hoareTime (L P : ℕ) (R : (Fin 6 → Tape) → Prop) (hR : Stable R)
    (s : SmallSyntaxControl.State) (hlen : s.input.length ≤ L) (hp : s.pending ≤ P) :
    machine.HoareTime (Inv R s) (Inv R (SmallSyntaxControl.step s)) (12 * L + 2 * P + 50) :=
  (hoareTime L R hR s hlen).mono_bound (by omega)

end JointThermoComplexity.Complexity.SmallSyntaxStep

#print axioms JointThermoComplexity.Complexity.SmallSyntaxStep.hoareTime
#print axioms JointThermoComplexity.Complexity.SmallSyntaxStep.bounded_hoareTime
