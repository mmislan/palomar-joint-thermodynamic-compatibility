module
public import proofs.JointThermoComplexity.Complexity.TallySpec
public import proofs.JointThermoComplexity.Complexity.ExponentArrayTally
public import proofs.JointThermoComplexity.Complexity.NaturalSkip

set_option autoImplicit false
@[expose] public section

/-! Concrete encoded-array and read-only factor instances of the tally contract. -/

namespace JointThermoComplexity.Complexity.TallyComponents
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend TallySpec

variable {w : ℕ}

theorem array_runs (fuel : Fin w) (values : List ℕ) :
    Runs (ExponentArrayTally.machine fuel) (fun work => IsReg values.length (work fuel))
      (ExponentArrayData.code values) (ExponentArrayData.cost values)
      (values.length * ((ExponentArrayData.code values).length + 6) + (values.length + 2)) := by
  intro count before tail emitted R
  have h := ExponentArrayTally.hoareTime fuel values count before tail emitted R
  exact h.consequence
    (fun _ _ _ ⟨hc, hs, hp, hz, hf, hr⟩ => ⟨hf, hc, hs, hp, hz, hr⟩)
    (fun _ _ _ ⟨hf, hc, hs, hp, hz, hr⟩ => ⟨hc, hs, hp, hz, hf, hr⟩) le_rfl

theorem skip_runs (value : ℕ) (Env : (Fin w → Tape) → Prop) :
    Runs NaturalSkip.machine Env (BitCodec.naturalCode value) 0 (BitCodec.naturalCode value).length := by
  intro count before tail emitted R
  have h := NaturalSkip.hoareTime (w := w + 1) value before tail emitted (fun work =>
    (work destination).HasBinaryPrefix (List.replicate count true) ∧ (work destination).cells 0 = Γ.start ∧
      Env (oldWork work) ∧ R (oldWork work))
  exact h.consequence
    (fun _ _ _ ⟨hc, hs, hp, hz, he, hr⟩ => ⟨hc, hs, hp, hz, he, hr⟩)
    (fun _ _ _ hp => by simpa only [State, Nat.add_zero] using hp) le_rfl

end JointThermoComplexity.Complexity.TallyComponents

#print axioms JointThermoComplexity.Complexity.TallyComponents.array_runs
#print axioms JointThermoComplexity.Complexity.TallyComponents.skip_runs
