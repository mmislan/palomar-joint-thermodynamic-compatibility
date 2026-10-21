module
public import proofs.JointThermoComplexity.Complexity.ActivityContinuation
public import proofs.JointThermoComplexity.Complexity.OuterActivityBoxBankFrame

set_option autoImplicit false
@[expose] public section

/-! The unchanged positivity emitter retains the blank production bank with its original runtime. -/

namespace JointThermoComplexity.Complexity.OuterActivityContinuationBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before remaining emitted : List Bool) :
    (ActivityStart.machine (m + 7)).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        CurrentReady.Ready (m + 7) input.length (NetworkMembership.arity Q.network) (Q.speciesCount + Q.reactionCount)
          Q.speciesCount (CurrentResources.State (m + 7) input) work ∧
        IsReg Q.reactionCount (work (ReactionFuel.slot (m + 7))) ∧ OuterFuelBank.State m work)
      (fun inp work out => Cursor before remaining (emitted ++ ActivityContinuation.word Q) inp work out ∧
        CurrentReady.Ready (m + 7) input.length (NetworkMembership.arity Q.network) Q.speciesCount
          Q.speciesCount (CurrentResources.State (m + 7) input) work ∧
        IsReg Q.reactionCount (work (ReactionFuel.slot (m + 7))) ∧ OuterFuelBank.State m work)
      (ActivityStart.timeBound input.length) := by
  let R : (Fin (m + 22) → Tape) → Prop := fun work =>
    IsReg (NetworkMembership.arity Q.network) (work (raw (m + 7))) ∧
    (∃ old, old ≤ 4 * input.length ∧ IsReg old (work (previous (m + 8)))) ∧
    IsReg Q.reactionCount (work (ReactionFuel.slot (m + 7))) ∧
    CurrentResources.State (m + 7) input work ∧ OuterFuelBank.State m work
  have hR : ∀ work work', (∀ j, j ≠ species (m + 8) → work' j = work j) → R work → R work' := by
    rintro work work' hw ⟨hv, ⟨old, hold, hp⟩, hf, hr, hb⟩
    exact ⟨by simpa only [hw _ (raw_ne_current (m + 7))] using hv,
      ⟨old, hold, by simpa only [hw _ (previous_ne_species (m + 8))] using hp⟩,
      by simpa only [hw _ (ReactionFuel.slot_separate (m + 7)).species] using hf,
      CurrentResources.frame (m + 7) input work work' (fun j _ _ hj => hw j hj) hr,
      OuterActivityBoxBankFrame.activity_frame m work work' hw hb⟩
  have hdim := NetworkCodec.decoded_dimensions_le_length hd
  have ht := ActivityStart.hoareTime (m + 7) input.length (Q.speciesCount + Q.reactionCount)
    (NetworkNumbering.decoded_arity_bound hd) (by omega) (by omega)
    (NetworkMembership.activityIndex Q.network) (fun _ => rfl) before remaining emitted R hR
  exact ht.consequence (by
    rintro inp work out ⟨hc, ⟨hs, hz, hv, hi, hp, hf, hr⟩, hreact, hb⟩
    exact ⟨hc, ⟨hs, hz, hi, hv, hp, hreact, hr, hb⟩, hf⟩) (by
    rintro inp work out ⟨hc, ⟨hs, hz, hi, hv, hp, hreact, hr, hb⟩, hf⟩
    exact ⟨hc, ⟨hs, hz, hv, hi, hp, hf, hr⟩, hreact, hb⟩) le_rfl

end JointThermoComplexity.Complexity.OuterActivityContinuationBank

#print axioms JointThermoComplexity.Complexity.OuterActivityContinuationBank.hoareTime
