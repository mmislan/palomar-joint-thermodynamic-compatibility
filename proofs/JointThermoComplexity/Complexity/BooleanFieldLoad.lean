module
public import proofs.JointThermoComplexity.Complexity.BooleanBufferLoad
public import proofs.JointThermoComplexity.Complexity.BoxBufferState

set_option autoImplicit false
@[expose] public section

/-! Load a bounded motif mask or orientation vector into an existing reusable binary buffer. -/

namespace JointThermoComplexity.Complexity.BooleanFieldLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState

variable {w : ℕ}

abbrev machine (e : Fin (w + 1) ≃ Fin (w + 1)) (r : Fin w) : TM (w + 1) := BooleanBufferLoad.machine e r

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (r : Fin w) (L : ℕ)
    (bits before tail emitted : List Bool) (hlen : bits.length ≤ L) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (machine e r).HoareTime
      (fun inp work out => Cursor before (bits ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Reusable L (work (CountSumAt.destination e)) ∧ IsReg bits.length (work (BooleanBufferAt.fuel e r)) ∧ R work)
      (fun inp work out => Cursor (before ++ bits) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Stored bits (work (CountSumAt.destination e)) ∧ Reusable L (work (CountSumAt.destination e)) ∧
        IsReg bits.length (work (BooleanBufferAt.fuel e r)) ∧ R work) (16 * L + 12) := by
  rintro inp work out ⟨hc, hsafe, ⟨old, hold, hcontent, hz, hhead⟩, hf, hr⟩
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdsafe, hdp, hdz, hdf, hdr⟩ :=
    BooleanBufferLoad.hoareTime e r old bits before tail emitted R hR inp work out
      ⟨hc, hsafe, hcontent, hz, hhead, hf, hr⟩
  have hstored : Stored bits (d.work (CountSumAt.destination e)) := ⟨hdp, hdz⟩
  exact ⟨d, t, by omega, hreach, hhalt, hdc, hdsafe, hstored, hstored.reusable (by omega), hdf, hdr⟩

end JointThermoComplexity.Complexity.BooleanFieldLoad

#print axioms JointThermoComplexity.Complexity.BooleanFieldLoad.hoareTime
