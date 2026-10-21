module
public import proofs.JointThermoComplexity.Complexity.DenseRawReady
public import proofs.JointThermoComplexity.Complexity.AddressCodeProgram

set_option autoImplicit false
@[expose] public section

/-! Bounded clearing of an actually reusable buffer; no renewed freshness or
canonical-value assumption is needed for unused source reference slots. -/

namespace JointThermoComplexity.Complexity.DenseReusableClear
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun BoxBufferState
variable {w : ℕ}

theorem hoareTime (idx : Fin w) (L : ℕ) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : BinaryIncrementFramed.Stable idx R) :
    (BinaryBufferReset.machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work idx) ∧ Reusable L (work idx) ∧ R work) (12 * L + 9) := by
  rintro inp work out ⟨hc, hs, ⟨bits, hlen, hcontent, hzero, hhead⟩, hr⟩
  have hh := BinaryBufferReset.hoareTime idx bits before input emitted R hR
  obtain ⟨d, time, ht, hreach, hhalt, hc', hs', hz, hr'⟩ := hh inp work out ⟨hc, hs, hcontent, hzero, hhead, hr⟩
  exact ⟨d, time, by omega, hreach, hhalt, hc', hs', AddressCodeProgram.binary_zero hz,
    BoxBufferState.of_register (Nat.zero_le _) hz, hr'⟩

end JointThermoComplexity.Complexity.DenseReusableClear

#print axioms JointThermoComplexity.Complexity.DenseReusableClear.hoareTime
