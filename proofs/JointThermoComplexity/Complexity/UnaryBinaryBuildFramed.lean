module
public import proofs.JointThermoComplexity.Complexity.UnaryBinaryBuild
public import proofs.JointThermoComplexity.Complexity.SafeExecution

set_option autoImplicit false
@[expose] public section

/-! Preserve the complete parked frame while building a bounded unary value's raw binary address. -/

namespace JointThermoComplexity.Complexity.UnaryBinaryBuildFramed
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
variable {w : ℕ}

theorem hoareTime (fuel dst : Fin w) (hne : fuel ≠ dst) (v : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ fuel → j ≠ dst → next j = work j) → R work → R next) :
    (UnaryBinaryBuild.machine fuel dst).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg v (work fuel) ∧ Register 0 (work dst) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg v (work fuel) ∧ Register v (work dst) ∧ R work)
      (v * (2 * v + 6) + (v + 2)) := by
  have h := UnaryBinaryBuild.hoareTime fuel dst hne v before input emitted R hR
  have hs := SafeExecution.hoareTime _ _ _ _ h (by
    rintro inp work out ⟨_, hc, _, _⟩ j
    exact (hc.works j).2)
  exact hs.consequence
    (fun _ _ _ ⟨hc, hs, hf, hd, hr⟩ => ⟨⟨hf, hc, hd, hr⟩, hs⟩)
    (fun _ _ _ ⟨⟨hf, hc, hd, hr⟩, hs⟩ => ⟨hc, hs, hf, hd, hr⟩) le_rfl

end JointThermoComplexity.Complexity.UnaryBinaryBuildFramed

#print axioms JointThermoComplexity.Complexity.UnaryBinaryBuildFramed.hoareTime
