module
public import proofs.JointThermoComplexity.Complexity.NetworkBuild
public import proofs.JointThermoComplexity.Complexity.ReactionDecodedBounds

set_option autoImplicit false
@[expose] public section

/-! Every runtime bound and address in the circuit generator is supplied by successful decoding of the actual network input. -/

namespace JointThermoComplexity.Complexity.NetworkDecodedBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts NetworkEmitReady
open CircuitSerialization PowerAddressCircuit FiniteCodec

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before tail initial : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → j ≠ saved m → work' j = work j) → R work → R work') :
    (NetworkBuild.machine m).HoareTime
      (fun inp work out => Cursor before (functionCode (DataCodec.reaction Q.speciesCount) Q.network.reactions ++ tail) initial inp work out ∧
        Ready m input.length (Q.speciesCount + Q.reactionCount) 0 Q.speciesCount R work ∧
        IsReg Q.reactionCount (work (ReactionFuel.slot m)))
      (fun inp work out => Cursor (before ++ functionCode (DataCodec.reaction Q.speciesCount) Q.network.reactions) tail
        (initial ++ equationStream (NetworkCircuit.dense Q.network.reactions).circuit
          (NetworkMembership.activityIndex Q.network) (NetworkMembership.auxiliaryIndex Q.network)) inp work out ∧
        Ready m input.length (Q.speciesCount + Q.reactionCount) (NetworkMembership.gates Q.network) Q.speciesCount R work ∧
        IsReg Q.reactionCount (work (ReactionFuel.slot m)))
      (ReactionLoopEntry.timeBound input.length) := by
  have hdim := NetworkCodec.decoded_dimensions_le_length hd
  have hfit : Q.speciesCount + Q.reactionCount + (NetworkCircuit.dense Q.network.reactions).size ≤
      NetworkMembership.arity Q.network := le_rfl
  have hi : index (Q.speciesCount + Q.reactionCount) _ (NetworkMembership.arity Q.network) hfit =
      NetworkMembership.auxiliaryIndex Q.network := by
    funext i
    apply Fin.ext
    rfl
  have ht := NetworkBuild.hoareTime m input.length (Q.speciesCount + Q.reactionCount)
    (NetworkMembership.arity Q.network) (NetworkNumbering.decoded_arity_bound hd) Q.network.reactions
    (NetworkMembership.activityIndex Q.network) (fun _ => rfl) hfit (by omega) (by omega)
    (fun j i => (MonomialDecodedBounds.exponent_bits hd j i).1)
    (fun j i => (MonomialDecodedBounds.exponent_bits hd j i).2)
    (fun j => (ReactionDecodedBounds.factor_fields hd j).1) (fun j => (ReactionDecodedBounds.factor_fields hd j).2)
    before tail initial R hR
  simpa only [hi] using ht

end JointThermoComplexity.Complexity.NetworkDecodedBuild

#print axioms JointThermoComplexity.Complexity.NetworkDecodedBuild.hoareTime
