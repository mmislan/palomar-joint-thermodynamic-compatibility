module
public import proofs.JointThermoComplexity.Complexity.NaturalSkip

set_option autoImplicit false
@[expose] public section

/-! Canonical natural-field traversal preserves arbitrary properties of the entire work and output tapes. -/

namespace JointThermoComplexity.Complexity.NaturalSkipExact
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

theorem hoareTime (value : ℕ) (before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (NaturalSkip.machine (w := w)).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧ R work out)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail emitted inp work out ∧ R work out)
      (BitCodec.naturalCode value).length := by
  rintro inp work out ⟨hc, hr⟩
  obtain ⟨e, t, ht, hreach, hhalt, hecur, hework, heout⟩ :=
    NaturalSkip.scan value.bits before tail emitted ⟨some false, inp, work, out⟩ rfl hc
  exact ⟨e, t, by simpa only [BitCodec.naturalCode, BitCodec.encodeBits_length] using ht,
    hreach, hhalt, hecur, by simpa only [hework, heout] using hr⟩

end JointThermoComplexity.Complexity.NaturalSkipExact

#print axioms JointThermoComplexity.Complexity.NaturalSkipExact.hoareTime
