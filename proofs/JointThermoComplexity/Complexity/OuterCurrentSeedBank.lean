module
public import proofs.JointThermoComplexity.Complexity.OuterCurrentBankFrame
public import proofs.JointThermoComplexity.Complexity.CurrentSeed

set_option autoImplicit false
@[expose] public section

/-! The existing current initializer establishes its usual state while retaining the actual reserved bank. -/

namespace JointThermoComplexity.Complexity.OuterCurrentSeedBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before remaining emitted : List Bool) :
    (CurrentStart.machine (m + 7)).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        NetworkEmitReady.Ready (m + 7) input.length (Q.speciesCount + Q.reactionCount) (NetworkMembership.gates Q.network)
          Q.speciesCount (NetworkPins.Kept (m + 7) input) work ∧ OuterFuelBank.State m work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        CurrentReady.Ready (m + 7) input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount Q.speciesCount
          (CurrentResources.State (m + 7) input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot (m + 7))) ∧ OuterFuelBank.State m work)
      (18 * input.length + 31) := by
  rintro inp work out ⟨hc, hready, hbank⟩
  have hresources := CurrentResources.of_network_ready (m + 7) input Q hd work hready
  rcases hready with ⟨hs, hz, _, _, hprev, _, ⟨idx, hidx, hi⟩, hf, hk⟩
  have hdim := NetworkCodec.decoded_dimensions_le_length hd
  have hoff : ArityValue.offset input = Q.speciesCount + Q.reactionCount := by
    obtain ⟨hs, hr, _⟩ := DecodedDimensions.decode_counts hd
    simp only [ArityValue.offset, hs, hr]
  let R : (Fin (m + 22) → Tape) → Prop := fun work => CurrentResources.State (m + 7) input work ∧ OuterFuelBank.State m work
  have ht := CurrentStart.hoareTime (m + 7) input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount
    (GateCountValue.count input) idx (by omega) (by omega) (GateCountValue.bound input) hidx
    before remaining emitted R (by
      rintro work work' hw ⟨hp, hb⟩
      exact ⟨CurrentResources.frame (m + 7) input work work' (fun j hraw _ hcurrent => hw j hraw hcurrent) hp,
        OuterCurrentBankFrame.start_frame m work work' hw hb⟩)
  obtain ⟨d, t, htime, hreach, hhalt, hdc, hdr⟩ := ht inp work out
    ⟨hc, hs, hz, hk.1, by simpa only [hoff] using hk.2.1, hi, hf, hprev, hresources, hbank⟩
  have hsplit := (OuterCurrentBankFrame.ready_and m input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount Q.speciesCount
    (CurrentResources.State (m + 7) input) (OuterFuelBank.State m) d.work).mp hdr
  have hmeta : CurrentResources.State (m + 7) input d.work := hsplit.1.2.2.2.2.2.2
  exact ⟨d, t, htime, hreach, hhalt, hdc, hsplit.1, (CurrentPins.counts (m + 7) input Q hd d.work hmeta.1).2, hsplit.2⟩

end JointThermoComplexity.Complexity.OuterCurrentSeedBank

#print axioms JointThermoComplexity.Complexity.OuterCurrentSeedBank.hoareTime
