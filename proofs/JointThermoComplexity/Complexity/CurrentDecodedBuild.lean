module
public import proofs.JointThermoComplexity.Complexity.CurrentDenseBuild
public import proofs.JointThermoComplexity.Complexity.ReactionDecodedBounds

set_option autoImplicit false
@[expose] public section

/-! Successful decoding supplies every bound for the exact complete current-equation machine. -/

namespace JointThermoComplexity.Complexity.CurrentDecodedBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts CurrentReady FiniteCodec

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ raw m → j ≠ previous (m + 1) → j ≠ species (m + 1) →
      work' j = work j) → R work → R work') :
    (CurrentDenseBuild.machine m).HoareTime
      (fun inp work out => Cursor before (functionCode (DataCodec.reaction Q.speciesCount) Q.network.reactions ++ tail) emitted inp work out ∧
        Ready m input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount Q.speciesCount R work ∧
        IsReg Q.reactionCount (work (ReactionFuel.slot m)))
      (fun inp work out => Cursor (before ++ functionCode (DataCodec.reaction Q.speciesCount) Q.network.reactions) tail
        (emitted ++ (NetworkMembership.equationsFormula Q.network).code) inp work out ∧
        Ready m input.length (NetworkMembership.arity Q.network) (Q.speciesCount + Q.reactionCount) Q.speciesCount R work ∧
        IsReg Q.reactionCount (work (ReactionFuel.slot m))) (CurrentDenseBuild.timeBound input.length) := by
  have hdim := NetworkCodec.decoded_dimensions_le_length hd
  have hfields : ∀ i, ((DataCodec.reaction Q.speciesCount).code (Q.network.reactions i)).length ≤ input.length := by
    intro i
    have hi := InputSize.reaction_length_le_input Q i
    rw [← NetworkCodec.decode_sound hd] at hi
    exact hi
  exact CurrentDenseBuild.hoareTime m input.length Q.network (NetworkNumbering.decoded_arity_bound hd)
    (by omega) (by omega) hfields before tail emitted R hR

end JointThermoComplexity.Complexity.CurrentDecodedBuild

#print axioms JointThermoComplexity.Complexity.CurrentDecodedBuild.hoareTime
