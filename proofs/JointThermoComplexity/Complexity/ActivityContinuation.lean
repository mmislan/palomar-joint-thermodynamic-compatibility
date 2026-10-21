module
public import proofs.JointThermoComplexity.Complexity.ActivityStart
public import proofs.JointThermoComplexity.Complexity.CurrentResources
public import proofs.JointThermoComplexity.Complexity.CurrentReady
public import proofs.JointThermoComplexity.Complexity.NetworkNumbering

set_option autoImplicit false
@[expose] public section

/-! The fresh circuit/current postcondition supplies and survives the complete leading positivity block of the constraint suffix. -/

namespace JointThermoComplexity.Complexity.ActivityContinuation
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts CircuitSerialization

def word (Q : NetworkCodec.Input) : List Bool :=
  conjunctionTag ++ (ActivityCode.formula (NetworkMembership.activityIndex Q.network)).code

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before remaining emitted : List Bool) :
    (ActivityStart.machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        CurrentReady.Ready m input.length (NetworkMembership.arity Q.network) (Q.speciesCount + Q.reactionCount)
          Q.speciesCount (CurrentResources.State m input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m)))
      (fun inp work out => Cursor before remaining (emitted ++ word Q) inp work out ∧
        CurrentReady.Ready m input.length (NetworkMembership.arity Q.network) Q.speciesCount
          Q.speciesCount (CurrentResources.State m input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m)))
      (ActivityStart.timeBound input.length) := by
  let R : (Fin (m + 15) → Tape) → Prop := fun work =>
    IsReg (NetworkMembership.arity Q.network) (work (raw m)) ∧
    (∃ old, old ≤ 4 * input.length ∧ IsReg old (work (previous (m + 1)))) ∧
    IsReg Q.reactionCount (work (ReactionFuel.slot m)) ∧ CurrentResources.State m input work
  have hR : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → R work → R work' := by
    rintro work work' hw ⟨hv, ⟨old, hold, hp⟩, hf, hr⟩
    exact ⟨by simpa only [hw _ (raw_ne_current m)] using hv,
      ⟨old, hold, by simpa only [hw _ (previous_ne_species (m + 1))] using hp⟩,
      by simpa only [hw _ (ReactionFuel.slot_separate m).species] using hf,
      CurrentResources.frame m input work work' (fun j _ _ hj => hw j hj) hr⟩
  have hdim := NetworkCodec.decoded_dimensions_le_length hd
  have ht := ActivityStart.hoareTime m input.length (Q.speciesCount + Q.reactionCount)
    (NetworkNumbering.decoded_arity_bound hd) (by omega) (by omega)
    (NetworkMembership.activityIndex Q.network) (fun _ => rfl) before remaining emitted R hR
  exact ht.consequence (by
    rintro inp work out ⟨hc, ⟨hs, hz, hv, hi, hp, hf, hr⟩, hreact⟩
    exact ⟨hc, ⟨hs, hz, hi, hv, hp, hreact, hr⟩, hf⟩) (by
    rintro inp work out ⟨hc, ⟨hs, hz, hi, hv, hp, hreact, hr⟩, hf⟩
    exact ⟨hc, ⟨hs, hz, hv, hi, hp, hf, hr⟩, hreact⟩) le_rfl

end JointThermoComplexity.Complexity.ActivityContinuation

#print axioms JointThermoComplexity.Complexity.ActivityContinuation.hoareTime
