module
public import proofs.JointThermoComplexity.Complexity.NetworkNumbering

set_option autoImplicit false
@[expose] public section

/-! The validated network input length bounds every monomial loop count and exponent payload. -/

namespace JointThermoComplexity.Complexity.MonomialDecodedBounds

theorem species {input : List Bool} {Q : NetworkCodec.Input} (h : NetworkCodec.decode input = some Q) :
    Q.speciesCount ≤ input.length := by
  have hd := NetworkCodec.decoded_dimensions_le_length h
  omega

theorem exponent_bits {input : List Bool} {Q : NetworkCodec.Input} (h : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) :
    ((Q.network.reactions i).reactant s).bits.length ≤ input.length ∧
      ((Q.network.reactions i).product s).bits.length ≤ input.length := by
  have hc := InputSize.complex_entries_le_input Q i s
  have hcode : Q.code.length = input.length := congrArg List.length (NetworkCodec.decode_sound h).symm
  simp only [BitCodec.naturalCode_length, hcode] at hc
  exact ⟨by omega, by omega⟩

end JointThermoComplexity.Complexity.MonomialDecodedBounds

#print axioms JointThermoComplexity.Complexity.MonomialDecodedBounds.exponent_bits
