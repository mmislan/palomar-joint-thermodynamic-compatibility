module
public import proofs.JointThermoComplexity.Complexity.PayloadFrame
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! A compositional binary-field copy preserves the entire work-tape family exactly. -/

namespace JointThermoComplexity.Complexity.PayloadCopy
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem hoareTime (w : ℕ) (bits before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (PayloadFrame.machine w).HoareTime
      (fun inp work out => Cursor before (BitCodec.encodeBits bits ++ tail) emitted inp work out ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.encodeBits bits) tail
        (emitted ++ BitCodec.encodeBits bits) inp work out ∧ R work) ((BitCodec.encodeBits bits).length + 2) := by
  rintro inp work out ⟨hc, hr⟩
  obtain ⟨d, t, ht, hreach, hhalt, hcells, hhead, hwork, hzero, hp⟩ := PayloadFrame.encoded_frame
    before emitted bits tail ⟨(PayloadFrame.machine w).qstart, inp, work, out⟩ rfl
    hc.cells hc.head (fun j => (hc.works j).1) hc.tapePrefix hc.zero
  refine ⟨d, t, ht, hreach, hhalt, ⟨?_, ?_, ?_, hp, hzero⟩, ?_⟩
  · simpa only [List.append_assoc] using hcells.trans hc.cells
  · simpa only [List.length_append] using hhead
  · simpa only [hwork] using hc.works
  · simpa only [hwork] using hr

end JointThermoComplexity.Complexity.PayloadCopy

#print axioms JointThermoComplexity.Complexity.PayloadCopy.hoareTime
