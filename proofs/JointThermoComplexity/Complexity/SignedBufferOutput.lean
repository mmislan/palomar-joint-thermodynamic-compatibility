module
public import proofs.JointThermoComplexity.Complexity.FlagBitOutput
public import proofs.JointThermoComplexity.Complexity.BinaryPayloadReplay

set_option autoImplicit false
@[expose] public section

/-! Serialize an actual retained sign and an end-parked canonical magnitude buffer. -/

namespace JointThermoComplexity.Complexity.SignedBufferOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (idx flag : Fin w) : TM w := seqTM (FlagBitOutput.machine flag) (BinaryPayloadReplay.machine idx)

theorem hoareTime (idx flag : Fin w) (hne : flag ≠ idx) (b : Bool)
    (bits before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix bits ∧ (work idx).cells 0 = Γ.start ∧ (work flag).read = Γ.ofBool b ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (b :: BitCodec.encodeBits bits)) inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ (work flag).read = Γ.ofBool b ∧ R work)
      (4 * bits.length + 13) := by
  let R' : (Fin w → Tape) → Prop := fun work => (work flag).read = Γ.ofBool b ∧ R work
  have hR' : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R' work → R' work' := by
    rintro work work' hw ⟨hf, hr⟩
    exact ⟨by simpa only [hw flag hne] using hf, hR work work' hw hr⟩
  have hs := FlagBitOutput.hoareTime flag b before input emitted
    (fun work => (work idx).HasBinaryPrefix bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
  have hp := BinaryPayloadReplay.hoareTime idx bits before input (emitted ++ [b]) R' hR'
  have hfull := seqTM_hoareTime (FlagBitOutput.machine flag) (BinaryPayloadReplay.machine idx) hs (by
    rintro inp work out ⟨hc, hs, hf, hb, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hb, hz, hf, hr⟩) hp
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hs, hb, hz, hf, hr⟩
    exact ⟨hc, hs, hf, hb, hz, hr⟩) (by
      intro inp work out h
      simpa only [List.append_assoc, List.singleton_append] using h) (by omega)

end JointThermoComplexity.Complexity.SignedBufferOutput

#print axioms JointThermoComplexity.Complexity.SignedBufferOutput.hoareTime
