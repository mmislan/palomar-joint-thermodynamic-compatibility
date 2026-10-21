module
public import proofs.JointThermoComplexity.Complexity.MotifDirectionState
public import proofs.JointThermoComplexity.Complexity.BinaryPrefixRewind

set_option autoImplicit false
@[expose] public section

/-! Rewind one completed motif vector and retain the complete bounded ready state. -/

namespace JointThermoComplexity.Complexity.MotifBufferRewind
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts MotifDirectionState BoxBufferState

theorem hoareTime (m L idx : ℕ) (k : Fin 3) (bits before input emitted : List Bool) (hlen : bits.length ≤ L)
    (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ buffer m k → work' j = work j) → R work → R work') :
    (rewindWorkTM (buffer m k)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ BoxState.Ready m L idx R work ∧ Stored bits (work (buffer m k)))
      (fun inp work out => Cursor before input emitted inp work out ∧ BoxState.Ready m L idx R work ∧ At bits 0 (work (buffer m k)))
      (bits.length + 3) := by
  rintro inp work out ⟨hc, hp, hs⟩
  let S : (Fin (m + 15) → Tape) → Prop := fun work' => ∀ j, j ≠ buffer m k → work' j = work j
  have hS : ∀ work₁ work₂, (∀ j, j ≠ buffer m k → work₂ j = work₁ j) → S work₁ → S work₂ := by
    intro work₁ work₂ hw hs j hj
    exact (hw j hj).trans (hs j hj)
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hsafe, hstring, hz, hdw⟩ :=
    BinaryPrefixRewind.hoareTime (buffer m k) bits before input emitted S hS inp work out
      ⟨hc, hp.1, hs.1, hs.2, fun _ _ => rfl⟩
  have hat : At bits 0 (d.work (buffer m k)) := ⟨hstring.2, hz, hstring.1⟩
  have hreusable : Reusable L (d.work (buffer m k)) := hat.reusable (by omega) (Nat.zero_le _)
  exact ⟨d, t, ht, hreach, hhalt, hdc, frame_ready m L idx k R hR work d.work hdw hsafe hreusable hp, hat⟩

end JointThermoComplexity.Complexity.MotifBufferRewind

#print axioms JointThermoComplexity.Complexity.MotifBufferRewind.hoareTime
