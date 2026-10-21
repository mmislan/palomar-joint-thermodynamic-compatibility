module
public import proofs.JointThermoComplexity.Complexity.SourceValidityRun
public import proofs.JointThermoComplexity.Complexity.InputRewind

set_option autoImplicit false
@[expose] public section

/-! Restore the original input cursor after total validity scanning, retaining the exact decoder flag and length fuel. -/

namespace JointThermoComplexity.Complexity.SourceValidityRewind
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceScannerPorts

def Kept (valid : Bool) (work : Fin 11 → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ (work (NaturalScanBuffer.flag 9)).read = Γ.ofBool valid

def Ready (input : List Bool) (work : Fin 11 → Tape) : Prop :=
  IsReg input.length (work fuel.castSucc) ∧ Kept (RealSyntax.decodeSentence input).isSome work

theorem full_word (input : List Bool) :
    (SourceSentenceEntry.finalState input.length [] input).before ++
      (SourceSentenceEntry.finalState input.length [] input).input = input := by
  have h := SourceFormulaLoopState.run_bounds (HeaderControl.count input) input.length input.length
    (SourceSentenceEntry.startState [] input)
  exact h.2.2.trans (HeaderControl.consumed_and_suffix input)

theorem before_bound (input : List Bool) :
    (SourceSentenceEntry.finalState input.length [] input).before.length ≤ input.length := by
  have h := congrArg List.length (full_word input)
  rw [List.length_append] at h
  omega

theorem hoareTime (input : List Bool) :
    (rewindInputTM (n := 11)).HoareTime (SourceValidityRun.Post input)
      (fun inp work out => Cursor [] input [] inp work out ∧ Ready input work) (input.length + 3) := by
  have h := InputRewind.hoareTime (SourceSentenceEntry.finalState input.length [] input).before
    (SourceSentenceEntry.finalState input.length [] input).input [] (Ready input)
  exact h.consequence (by
    rintro inp work out hp
    exact ⟨hp.1.1, hp.2, hp.1.2.1.base.safe, SourceValidityRun.post_status input inp work out hp⟩)
    (by intro inp work out hp; simpa only [full_word] using hp) (by have := before_bound input; omega)

end JointThermoComplexity.Complexity.SourceValidityRewind

#print axioms JointThermoComplexity.Complexity.SourceValidityRewind.full_word
#print axioms JointThermoComplexity.Complexity.SourceValidityRewind.hoareTime
