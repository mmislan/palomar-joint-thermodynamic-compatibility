module
public import proofs.JointThermoComplexity.Complexity.CurrentStart
public import proofs.JointThermoComplexity.Complexity.CurrentPins
public import proofs.JointThermoComplexity.Complexity.CurrentResources
public import proofs.JointThermoComplexity.Complexity.NetworkEmitReady

set_option autoImplicit false
@[expose] public section

/-! The checked circuit-pass postcondition supplies every current-rescan initialization input. -/

namespace JointThermoComplexity.Complexity.CurrentSeed
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before remaining emitted : List Bool) :
    (CurrentStart.machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        NetworkEmitReady.Ready m input.length (Q.speciesCount + Q.reactionCount) (NetworkMembership.gates Q.network)
          Q.speciesCount (NetworkPins.Kept m input) work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧
        CurrentReady.Ready m input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount Q.speciesCount
          (CurrentResources.State m input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m)))
      (18 * input.length + 31) := by
  intro inp work out hp
  obtain ⟨hc, hready⟩ := hp
  have hresources := CurrentResources.of_network_ready m input Q hd work hready
  rcases hready with ⟨hs, hz, _, _, hprev, _, ⟨idx, hidx, hi⟩, hf, hk⟩
  have hdim := NetworkCodec.decoded_dimensions_le_length hd
  have hoff : ArityValue.offset input = Q.speciesCount + Q.reactionCount := by
    obtain ⟨hs, hr, _⟩ := DecodedDimensions.decode_counts hd
    simp only [ArityValue.offset, hs, hr]
  have ht := CurrentStart.hoareTime m input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount
    (GateCountValue.count input) idx (by omega) (by omega) (GateCountValue.bound input) hidx
    before remaining emitted (CurrentResources.State m input)
    (fun work work' hw hp => CurrentResources.frame m input work work' (fun j hraw _ hcurrent => hw j hraw hcurrent) hp)
  obtain ⟨d, t, htime, hreach, hhalt, hdc, hdr⟩ := ht inp work out
    ⟨hc, hs, hz, hk.1, by simpa only [hoff] using hk.2.1, hi, hf, hprev, hresources⟩
  have hmeta : CurrentResources.State m input d.work := hdr.2.2.2.2.2.2
  exact ⟨d, t, htime, hreach, hhalt, hdc, hdr, (CurrentPins.counts m input Q hd d.work hmeta.1).2⟩

end JointThermoComplexity.Complexity.CurrentSeed

#print axioms JointThermoComplexity.Complexity.CurrentSeed.hoareTime
