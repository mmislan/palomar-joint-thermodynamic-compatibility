module
public import proofs.JointThermoComplexity.Complexity.NetworkDecodedBuild
public import proofs.JointThermoComplexity.Complexity.NetworkFreshRegisters
public import proofs.JointThermoComplexity.Complexity.NetworkPins

set_option autoImplicit false
@[expose] public section

/-! Wire the actual validated formula entry to the complete dense network circuit generator. -/

namespace JointThermoComplexity.Complexity.NetworkCircuitBody
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts NetworkEmitReady FiniteCodec CircuitSerialization

def table (Q : NetworkCodec.Input) : List Bool := functionCode (DataCodec.reaction Q.speciesCount) Q.network.reactions

theorem input_split (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q) :
    input = NetworkTallyData.headers Q ++ (table Q ++ NetworkTallyData.tail Q) := by
  rw [NetworkCodec.decode_sound hd, NetworkTallyData.code_split]
  unfold table NetworkTallyData.reactions
  rw [← ReactionArrayData.finiteFunction_code]
  rfl

def machine (m : ℕ) : TM (m + 15) :=
  seqTM (NetworkSeed.machine m) (seqTM DimensionSkip.machine (NetworkBuild.machine m))

def timeBound (L : ℕ) : ℕ := ReactionLoopEntry.timeBound L + 6 * L + 22

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        FormulaStart.Registers (m + 7) input work)
      (fun inp work out => Cursor (NetworkTallyData.headers Q ++ table Q) (NetworkTallyData.tail Q)
        (emitted ++ equationStream (NetworkCircuit.dense Q.network.reactions).circuit
          (NetworkMembership.activityIndex Q.network) (NetworkMembership.auxiliaryIndex Q.network)) inp work out ∧
        Ready m input.length (Q.speciesCount + Q.reactionCount) (NetworkMembership.gates Q.network) Q.speciesCount
          (NetworkPins.Kept m input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m)))
      (timeBound input.length) := by
  have hdim := NetworkCodec.decoded_dimensions_le_length hd
  have hoff : ArityValue.offset input = Q.speciesCount + Q.reactionCount := by
    obtain ⟨hs, hr, _⟩ := DecodedDimensions.decode_counts hd
    simp only [ArityValue.offset, hs, hr]
  let P : (Fin (m + 15) → Tape) → Prop := fun work =>
    Ready m input.length (Q.speciesCount + Q.reactionCount) 0 Q.speciesCount (NetworkPins.Kept m input) work ∧
      IsReg Q.reactionCount (work (ReactionFuel.slot m))
  have hseed := NetworkSeed.hoareTime m input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount
    (by omega) [] input emitted (NetworkPins.Kept m input)
    (fun work work' hw hp => NetworkPins.frame m input work work' (fun j hn _ _ _ _ _ _ => hw j hn) hp)
  have hskip := DimensionSkip.hoareTime Q.speciesCount Q.reactionCount Q.coreCount []
    (table Q ++ NetworkTallyData.tail Q) emitted P
  have hbuild := NetworkDecodedBuild.hoareTime m input Q hd (NetworkTallyData.headers Q) (NetworkTallyData.tail Q)
    emitted (NetworkPins.Kept m input) (NetworkPins.frame m input)
  have hrest := seqTM_hoareTime DimensionSkip.machine (NetworkBuild.machine m) hskip (by
    rintro inp work out ⟨hc, _, hr, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [List.nil_append, table, NetworkTallyData.headers] using hc, hr, hf⟩) hbuild
  have hfull := seqTM_hoareTime (NetworkSeed.machine m)
    (seqTM DimensionSkip.machine (NetworkBuild.machine m)) hseed (by
      rintro inp work out ⟨hc, hr⟩
      have hk : NetworkPins.Kept m input work := hr.2.2.2.2.2.2.2.2
      have hf := (NetworkPins.counts m input Q hd work hk).2
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨by simpa only [input_split input Q hd, NetworkTallyData.headers] using hc, hr.1, hr, hf⟩) hrest
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hs, hg, ho, hb, hk, hsp⟩
    have hp : NetworkPins.Kept m input work := ⟨hg, ho, hb, hk⟩
    obtain ⟨hn, hz, ht, hprev, hspecies, hsave⟩ := NetworkFreshRegisters.zeros m input.length work hsp
    have hf := (NetworkPins.counts m input Q hd work hp).1
    exact ⟨hc, hs, hz, hn, by simpa only [hoff] using ho, ht, hprev, hspecies, hsave, hf, hp⟩)
    (fun _ _ _ hp => hp) (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.NetworkCircuitBody

#print axioms JointThermoComplexity.Complexity.NetworkCircuitBody.hoareTime
