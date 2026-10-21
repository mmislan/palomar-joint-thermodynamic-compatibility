module
public import proofs.JointThermoComplexity.Complexity.MonomialDecodedBounds

set_option autoImplicit false
@[expose] public section

/-! Validated binary network input bounds both runtime rational-factor fields. -/

namespace JointThermoComplexity.Complexity.ReactionDecodedBounds

theorem factor_fields {input : List Bool} {Q : NetworkCodec.Input} (h : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) :
    (BitCodec.naturalCode (Q.network.reactions i).numerator).length ≤ input.length ∧
      (BitCodec.naturalCode (Q.network.reactions i).denominator).length ≤ input.length := by
  have hr := InputSize.reaction_length_le_input Q i
  rw [InputSize.reaction_code_length] at hr
  have hcode : Q.code.length = input.length := congrArg List.length (NetworkCodec.decode_sound h).symm
  rw [hcode] at hr
  exact ⟨by omega, by omega⟩

end JointThermoComplexity.Complexity.ReactionDecodedBounds

#print axioms JointThermoComplexity.Complexity.ReactionDecodedBounds.factor_fields
