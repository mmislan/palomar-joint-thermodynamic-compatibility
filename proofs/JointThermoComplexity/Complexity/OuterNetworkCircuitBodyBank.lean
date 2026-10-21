module
public import proofs.JointThermoComplexity.Complexity.OuterFuelBank
public import proofs.JointThermoComplexity.Complexity.NetworkCircuitBody

set_option autoImplicit false
@[expose] public section

/-! The existing valid-input circuit body retains the seven reserved production tapes with its original runtime. -/

namespace JointThermoComplexity.Complexity.OuterNetworkCircuitBodyBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts NetworkEmitReady CircuitSerialization

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) :
    (NetworkCircuitBody.machine (m + 7)).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        FormulaStart.Registers (m + 14) input work ∧ OuterFuelBank.State m work)
      (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
        (emitted ++ equationStream (NetworkCircuit.dense Q.network.reactions).circuit
          (NetworkMembership.activityIndex Q.network) (NetworkMembership.auxiliaryIndex Q.network)) inp work out ∧
        Ready (m + 7) input.length (Q.speciesCount + Q.reactionCount) (NetworkMembership.gates Q.network) Q.speciesCount
          (NetworkPins.Kept (m + 7) input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot (m + 7))) ∧ OuterFuelBank.State m work)
      (NetworkCircuitBody.timeBound input.length) := by
  have hdim := NetworkCodec.decoded_dimensions_le_length hd
  have hoff : ArityValue.offset input = Q.speciesCount + Q.reactionCount := by
    obtain ⟨hs, hr, _⟩ := DecodedDimensions.decode_counts hd
    simp only [ArityValue.offset, hs, hr]
  let R : (Fin (m + 22) → Tape) → Prop := fun work => NetworkPins.Kept (m + 7) input work ∧ OuterFuelBank.State m work
  let P : (Fin (m + 22) → Tape) → Prop := fun work =>
    Ready (m + 7) input.length (Q.speciesCount + Q.reactionCount) 0 Q.speciesCount R work ∧
      IsReg Q.reactionCount (work (ReactionFuel.slot (m + 7)))
  have hseed := NetworkSeed.hoareTime (m + 7) input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount
    (by omega) [] input emitted R (by
      rintro work work' hw ⟨hp, hb⟩
      exact ⟨NetworkPins.frame (m + 7) input work work' (fun j hn _ _ _ _ _ _ => hw j hn) hp,
        OuterFuelBank.seed_frame m work work' hw hb⟩)
  have hskip := DimensionSkip.hoareTime Q.speciesCount Q.reactionCount Q.coreCount []
    (NetworkCircuitBody.table Q ++ NetworkTallyData.tail Q) emitted P
  have hbuild := NetworkDecodedBuild.hoareTime (m + 7) input Q hd (NetworkTallyData.headers Q) (NetworkTallyData.tail Q)
    emitted R (by
      rintro work work' hw ⟨hp, hb⟩
      exact ⟨NetworkPins.frame (m + 7) input work work' hw hp, OuterFuelBank.network_frame m work work' hw hb⟩)
  have hrest := seqTM_hoareTime DimensionSkip.machine (NetworkBuild.machine (m + 7)) hskip (by
    rintro inp work out ⟨hc, _, hr, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [List.nil_append, NetworkCircuitBody.table, NetworkTallyData.headers] using hc, hr, hf⟩) hbuild
  have hfull := seqTM_hoareTime (NetworkSeed.machine (m + 7))
    (seqTM DimensionSkip.machine (NetworkBuild.machine (m + 7))) hseed (by
      rintro inp work out ⟨hc, hr⟩
      have hk : NetworkPins.Kept (m + 7) input work := hr.2.2.2.2.2.2.2.2.1
      have hf := (NetworkPins.counts (m + 7) input Q hd work hk).2
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨by simpa only [NetworkCircuitBody.input_split input Q hd, NetworkTallyData.headers] using hc, hr.1, hr, hf⟩) hrest
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hs, ⟨hg, ho, hb, hk, hsp⟩, hbank⟩
    have hp : NetworkPins.Kept (m + 7) input work := ⟨hg, ho, hb, hk⟩
    obtain ⟨hn, hz, ht, hprev, hspecies, hsave⟩ := NetworkFreshRegisters.zeros (m + 7) input.length work hsp
    have hf := (NetworkPins.counts (m + 7) input Q hd work hp).1
    exact ⟨hc, hs, hz, hn, by simpa only [hoff] using ho, ht, hprev, hspecies, hsave, hf, hp, hbank⟩) (by
      rintro inp work out ⟨hc, hp, hf⟩
      have h := (OuterFuelBank.network_ready_and m input.length (Q.speciesCount + Q.reactionCount)
        (NetworkMembership.gates Q.network) Q.speciesCount (NetworkPins.Kept (m + 7) input) (OuterFuelBank.State m) work).mp hp
      exact ⟨hc, h.1, hf, h.2⟩) (by unfold NetworkCircuitBody.timeBound; omega)

end JointThermoComplexity.Complexity.OuterNetworkCircuitBodyBank

#print axioms JointThermoComplexity.Complexity.OuterNetworkCircuitBodyBank.hoareTime
