module
public import proofs.JointThermoComplexity.Complexity.FlagBranchRun
public import proofs.JointThermoComplexity.Complexity.FixedOutput

set_option autoImplicit false
@[expose] public section

/-! Emit exactly one actual retained flag bit without changing any work tape. -/

namespace JointThermoComplexity.Complexity.FlagBitOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (flag : Fin w) : TM w := FlagBranch.machine flag (emitBitsTM [true]) (emitBitsTM [false])

theorem hoareTime (flag : Fin w) (b : Bool) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ (work flag).read = Γ.ofBool b ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ [b]) inp work out ∧ (∀ j, Parked (work j)) ∧ (work flag).read = Γ.ofBool b ∧ R work) 3 := by
  let P : (Fin w → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ (work flag).read = Γ.ofBool b ∧ R work
  have hbit (bit : Bool) := FixedOutput.hoareTime [bit] before input emitted
    (fun work => (work flag).read = Γ.ofBool b ∧ R work)
  cases b
  · have h := FlagBranchRun.no_hoareTime flag (emitBitsTM [true]) (emitBitsTM [false])
      before input emitted before input (emitted ++ [false]) P P 1 (hbit false)
    exact h.consequence (by
      rintro inp work out ⟨hc, hs, hf, hr⟩
      exact ⟨⟨hc, hs, hf, hr⟩, hf⟩) (fun _ _ _ h => h) le_rfl
  · have h := FlagBranchRun.yes_hoareTime flag (emitBitsTM [true]) (emitBitsTM [false])
      before input emitted before input (emitted ++ [true]) P P 1 (hbit true)
    exact h.consequence (by
      rintro inp work out ⟨hc, hs, hf, hr⟩
      exact ⟨⟨hc, hs, hf, hr⟩, hf⟩) (fun _ _ _ h => h) (by omega)

end JointThermoComplexity.Complexity.FlagBitOutput

#print axioms JointThermoComplexity.Complexity.FlagBitOutput.hoareTime
