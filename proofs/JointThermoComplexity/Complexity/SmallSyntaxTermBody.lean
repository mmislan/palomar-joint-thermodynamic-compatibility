module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxFields

set_option autoImplicit false
@[expose] public section

/-! Actual selected term branches expand integers and update the pending register after each source token. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxTermBody
open _root_.Complexity _root_.Complexity.TM SmallSyntaxRegisters
open HeaderAt (Cursor)

def after (s : SmallSyntaxControl.State) (next : SmallSyntaxToken.Token) : SmallSyntaxControl.State :=
  ⟨s.before ++ next.taken, next.rest, s.emitted ++ next.output, next.pending⟩

theorem seq_inv_hoareTime (a b : TM 6) (R : (Fin 6 → Tape) → Prop)
    (s u v : SmallSyntaxControl.State) (ta tb : ℕ)
    (ha : a.HoareTime (Inv R s) (Inv R u) ta) (hb : b.HoareTime (Inv R u) (Inv R v) tb) :
    (seqTM a b).HoareTime (Inv R s) (Inv R v) (ta + 1 + tb) :=
  seqTM_hoareTime a b ha (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hb

def integerMachine : TM 6 := seqTM (SmallIntegerStreamRun.machine (tags 0) flag) (SmallSyntaxCounter.move false)
def variableMachine (bits : List Bool) : TM 6 :=
  seqTM (emitBitsTM bits) (seqTM (NaturalMachine.machine false 5) (SmallSyntaxCounter.move false))
def binaryMachine (bits : List Bool) : TM 6 := seqTM (emitBitsTM bits) (SmallSyntaxCounter.move true)

def machine (bits : List Bool) : TM 6 := match SourceTermToken.classify bits with
  | .integer => integerMachine
  | .variable => variableMachine bits
  | .add | .mul => binaryMachine bits
  | .neg => emitBitsTM bits
  | .invalid => emitBitsTM []

theorem integer_hoareTime (L v : ℕ) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    integerMachine.HoareTime (Inv R ⟨before, input, emitted, v + 1⟩)
      (Inv R ⟨before ++ SmallIntegerStream.taken input, SmallIntegerStream.rest input,
        emitted ++ SmallIntegerStream.output input, v⟩) (12 * L + 2 * v + 26) := by
  have hf := SmallSyntaxFields.integer_hoareTime R hR ⟨before, input, emitted, v + 1⟩
  have hc := SmallSyntaxCounter.move_hoareTime false v (before ++ SmallIntegerStream.taken input)
    (SmallIntegerStream.rest input) (emitted ++ SmallIntegerStream.output input) R hR
  have h := seq_inv_hoareTime _ _ R _ _ _ _ _ hf hc
  simpa only [integerMachine, SmallSyntaxCounter.nextCount, Bool.false_eq_true, ↓reduceIte] using h.mono_bound (by omega :
    12 * input.length + 13 + 1 + (2 * v + 12) ≤ 12 * L + 2 * v + 26)

theorem variable_hoareTime (bits : List Bool) (hbits : bits.length = 3) (L v : ℕ)
    (before input emitted : List Bool) (hlen : input.length ≤ L) (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    (variableMachine bits).HoareTime (Inv R ⟨before, input, emitted, v + 1⟩)
      (Inv R ⟨before ++ PayloadControl.copied .empty input, NumericCursor.naturalRest input,
        (emitted ++ bits) ++ PayloadControl.copied .empty input, v⟩) (12 * L + 2 * v + 26) := by
  have he := emit_hoareTime bits R ⟨before, input, emitted, v + 1⟩
  have hf := SmallSyntaxFields.natural_hoareTime R hR ⟨before, input, emitted ++ bits, v + 1⟩
  have hc := SmallSyntaxCounter.move_hoareTime false v (before ++ PayloadControl.copied .empty input)
    (NumericCursor.naturalRest input) ((emitted ++ bits) ++ PayloadControl.copied .empty input) R hR
  have hfc := seq_inv_hoareTime _ _ R _ _ _ _ _ hf hc
  have h := seq_inv_hoareTime _ _ R _ _ _ _ _ he hfc
  simpa only [variableMachine, SmallSyntaxCounter.nextCount, Bool.false_eq_true, ↓reduceIte] using h.mono_bound (by omega :
    bits.length + 1 + (input.length + 2 + 1 + (2 * v + 12)) ≤ 12 * L + 2 * v + 26)

theorem binary_hoareTime (bits : List Bool) (hbits : bits.length = 3) (L v : ℕ)
    (before input emitted : List Bool) (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    (binaryMachine bits).HoareTime (Inv R ⟨before, input, emitted, v + 1⟩)
      (Inv R ⟨before, input, emitted ++ bits, v + 2⟩) (12 * L + 2 * v + 26) := by
  have he := emit_hoareTime bits R ⟨before, input, emitted, v + 1⟩
  have hc := SmallSyntaxCounter.move_hoareTime true v before input (emitted ++ bits) R hR
  have h := seq_inv_hoareTime _ _ R _ _ _ _ _ he hc
  simpa only [binaryMachine, SmallSyntaxCounter.nextCount, ↓reduceIte] using h.mono_bound (by omega :
    bits.length + 1 + (2 * v + 12) ≤ 12 * L + 2 * v + 26)

theorem hoareTime (bits : List Bool) (hbits : bits.length = 3) (L v : ℕ)
    (before input emitted : List Bool) (hlen : input.length ≤ L) (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    (machine bits).HoareTime (Inv R ⟨before, input, emitted, v + 1⟩)
      (Inv R (after ⟨before, input, emitted, v + 1⟩ (SmallSyntaxToken.termBody v bits input))) (12 * L + 2 * v + 26) := by
  cases hk : SourceTermToken.classify bits with
  | integer =>
    simpa only [machine, after, SmallSyntaxToken.termBody, hk] using integer_hoareTime L v before input emitted hlen R hR
  | «variable» =>
    simpa only [machine, after, SmallSyntaxToken.termBody, hk, List.append_assoc] using
      variable_hoareTime bits hbits L v before input emitted hlen R hR
  | add | mul =>
    simpa only [machine, after, SmallSyntaxToken.termBody, hk, List.append_nil] using
      binary_hoareTime bits hbits L v before input emitted R hR
  | neg =>
    have h := emit_hoareTime bits R ⟨before, input, emitted, v + 1⟩
    simpa only [machine, after, SmallSyntaxToken.termBody, hk, List.append_nil] using
      h.mono_bound (by omega : bits.length ≤ 12 * L + 2 * v + 26)
  | invalid =>
    have h := emit_hoareTime [] R ⟨before, input, emitted, v + 1⟩
    simpa only [machine, after, SmallSyntaxToken.termBody, hk, List.append_nil] using
      h.mono_bound (by omega : 0 ≤ 12 * L + 2 * v + 26)

end JointThermoComplexity.Complexity.SmallSyntaxTermBody

#print axioms JointThermoComplexity.Complexity.SmallSyntaxTermBody.hoareTime
