module
public import proofs.JointThermoComplexity.Complexity.FixedOutput
public import proofs.JointThermoComplexity.Complexity.NetworkInputControl

set_option autoImplicit false
@[expose] public section

/-! Exact false-sentence output for the rejecting branch of formula generation. -/

namespace JointThermoComplexity.Complexity.FalseOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt RealSyntax

variable {w : ℕ}

def sentence : Sentence := ⟨0, .falsity⟩
def machine : TM w := emitBitsTM sentence.code

theorem code_eq : sentence.code = [false, false, false, true] := rfl

theorem code_of_rejected (input : List Bool) (h : NetworkInputControl.accepted input = false) :
    (NetworkCodec.toSentence input).code = sentence.code := by
  have hd : NetworkCodec.decode input = none := by
    cases he : NetworkCodec.decode input with
    | none => rfl
    | some Q =>
      have ha := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, he⟩
      simp only [h, Bool.false_eq_true] at ha
  simp only [NetworkCodec.toSentence, hd, sentence]

theorem hoareTime (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ sentence.code) inp work out ∧
        (∀ j, Parked (work j)) ∧ R work) 4 := by
  simpa only [machine, code_eq, List.length_cons, List.length_nil] using
    FixedOutput.hoareTime sentence.code before input emitted R

theorem rejected_hoareTime (input emitted : List Bool) (h : NetworkInputControl.accepted input = false)
    (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor [] input (emitted ++ (NetworkCodec.toSentence input).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ R work) 4 := by
  simpa only [code_of_rejected input h] using hoareTime [] input emitted R

end JointThermoComplexity.Complexity.FalseOutput

#print axioms JointThermoComplexity.Complexity.FalseOutput.rejected_hoareTime
