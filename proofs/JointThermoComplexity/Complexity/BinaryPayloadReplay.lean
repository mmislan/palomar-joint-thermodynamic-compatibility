module
public import proofs.JointThermoComplexity.Complexity.BinaryPrefixRewind
public import proofs.JointThermoComplexity.Complexity.BinaryEmit

set_option autoImplicit false
@[expose] public section

/-! Emit a self-delimiting payload from an end-parked buffer, retaining its canonical contents. -/

namespace JointThermoComplexity.Complexity.BinaryPayloadReplay
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (idx : Fin w) : TM w := seqTM (rewindWorkTM idx) (BinaryEmit.machine idx)

theorem hoareTime (idx : Fin w) (bits before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ BitCodec.encodeBits bits) inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work) (4 * bits.length + 9) := by
  have hr := BinaryPrefixRewind.hoareTime idx bits before input emitted R hR
  have he := BinaryEmit.hoareTime idx bits before input emitted (fun work => (∀ j, Parked (work j)) ∧ R work)
  have hs := seqTM_hoareTime (rewindWorkTM idx) (BinaryEmit.machine idx) hr (by
    rintro inp work out ⟨hc, hs, hb, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hb, hz, hs, hr⟩) he
  exact hs.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hb, hz, hs, hr⟩
    exact ⟨hc, hs, hb, hz, hr⟩) (by omega)

end JointThermoComplexity.Complexity.BinaryPayloadReplay

#print axioms JointThermoComplexity.Complexity.BinaryPayloadReplay.hoareTime
