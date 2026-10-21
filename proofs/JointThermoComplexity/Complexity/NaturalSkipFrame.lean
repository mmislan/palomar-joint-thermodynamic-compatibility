module
public import proofs.JointThermoComplexity.Complexity.NaturalSkipExact
public import proofs.JointThermoComplexity.Complexity.ReadOnlyFrame

set_option autoImplicit false
@[expose] public section

/-! A canonical natural field can be skipped inside an outer register loop without disturbing its fuel head. -/

namespace JointThermoComplexity.Complexity.NaturalSkipFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop

variable {w : ℕ}

theorem hoareTime (r : Fin w) (v head : ℕ) (hh : 1 ≤ head) (value : ℕ)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (NaturalSkip.machine (w := w)).HoareTime
      (Frame r v head (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧ R work out))
      (Frame r v head (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail emitted inp work out ∧ R work out))
      (BitCodec.naturalCode value).length := by
  have hs := ReadOnlyFrame.hoareTime (NaturalSkip.machine (w := w)) r v head hh
    (BitCodec.naturalCode value) before tail emitted (fun _ => True) (BitCodec.naturalCode value).length
    (fun _ _ _ _ => trivial) (fun S => (NaturalSkipExact.hoareTime value before tail emitted S).consequence
      (fun _ _ _ ⟨hc, _, hr⟩ => ⟨hc, hr⟩) (fun _ _ _ ⟨hc, hr⟩ => ⟨hc, trivial, hr⟩) le_rfl) R
  exact hs.consequence (by
    intro inp work out hp
    exact ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, hp.invariant.1, trivial, hp.invariant.2⟩) (by
      intro inp work out hp
      exact ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, hp.invariant.1, hp.invariant.2.2⟩) le_rfl

end JointThermoComplexity.Complexity.NaturalSkipFrame

#print axioms JointThermoComplexity.Complexity.NaturalSkipFrame.hoareTime
