module
public import proofs.JointThermoComplexity.Complexity.RepeatedOutput
public import proofs.JointThermoComplexity.Complexity.RealSyntax

set_option autoImplicit false
@[expose] public section

/-! The exact unary existential-binder header, driven by a bounded count register. -/

namespace JointThermoComplexity.Complexity.BinderOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt RealSyntax

variable {w : ℕ}

def machine (fuel : Fin w) : TM w := seqTM (RepeatedOutput.machine fuel [true]) (emitBitsTM [false])

theorem hoareTime (fuel : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine fuel).HoareTime
      (fun inp work out => IsReg v (work fuel) ∧ Cursor before input emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => IsReg v (work fuel) ∧ Cursor before input (emitted ++ binderCode v) inp work out ∧
        (∀ j, Parked (work j)) ∧ R work) (4 * v + 4) := by
  let RP : (Fin w → Tape) → Prop := fun work => IsReg v (work fuel) ∧ R work
  have hrepeat := RepeatedOutput.hoareTime fuel v before input emitted [true] R
  have hend := FixedOutput.hoareTime [false] before input (emitted ++ RepeatedOutput.copies [true] v) RP
  have hseq := seqTM_hoareTime (RepeatedOutput.machine fuel [true]) (emitBitsTM [false]) hrepeat (by
    rintro inp work out ⟨hf, hc, hs, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hf, hr⟩) hend
  apply HoareTime.mono_bound (b := (v * ([true].length + 2) + (v + 2)) + 1 + [false].length)
  · apply HoareTime.strengthen_post hseq
    rintro inp work out ⟨hc, hs, hf, hr⟩
    exact ⟨hf, by simpa only [RepeatedOutput.copies_singleton, binderCode, List.append_assoc] using hc, hs, hr⟩
  · simp only [List.length_cons, List.length_nil]
    omega

end JointThermoComplexity.Complexity.BinderOutput

#print axioms JointThermoComplexity.Complexity.BinderOutput.hoareTime
