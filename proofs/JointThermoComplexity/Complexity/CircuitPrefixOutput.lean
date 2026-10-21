module
public import proofs.JointThermoComplexity.Complexity.CircuitSerialization

set_option autoImplicit false
@[expose] public section

/-! Emit the counted conjunction prefix and truth of the forward circuit serialization. -/

namespace JointThermoComplexity.Complexity.CircuitPrefixOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CircuitSerialization

variable {w : ℕ}

def machine (fuel : Fin w) : TM w :=
  seqTM (RepeatedOutput.machine fuel conjunctionTag) (emitBitsTM [false, false, false])

theorem hoareTime (fuel : Fin w) (gates : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine fuel).HoareTime
      (fun inp work out => IsReg gates (work fuel) ∧ Cursor before input emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => IsReg gates (work fuel) ∧
        Cursor before input (emitted ++ (RepeatedOutput.copies conjunctionTag gates ++ [false, false, false])) inp work out ∧
        (∀ j, Parked (work j)) ∧ R work) (6 * gates + 6) := by
  let RP : (Fin w → Tape) → Prop := fun work => IsReg gates (work fuel) ∧ R work
  have hrepeat := RepeatedOutput.hoareTime fuel gates before input emitted conjunctionTag R
  have htruth := FixedOutput.hoareTime [false, false, false] before input
    (emitted ++ RepeatedOutput.copies conjunctionTag gates) RP
  have hseq := seqTM_hoareTime (RepeatedOutput.machine fuel conjunctionTag) (emitBitsTM [false, false, false]) hrepeat (by
    rintro inp work out ⟨hf, hc, hs, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hf, hr⟩) htruth
  apply HoareTime.mono_bound (b := (gates * (conjunctionTag.length + 2) + (gates + 2)) + 1 + [false, false, false].length)
  · apply HoareTime.strengthen_post hseq
    rintro inp work out ⟨hc, hs, hf, hr⟩
    exact ⟨hf, by simpa only [List.append_assoc] using hc, hs, hr⟩
  · simp only [conjunctionTag, List.length_cons, List.length_nil]
    omega

end JointThermoComplexity.Complexity.CircuitPrefixOutput

#print axioms JointThermoComplexity.Complexity.CircuitPrefixOutput.hoareTime
