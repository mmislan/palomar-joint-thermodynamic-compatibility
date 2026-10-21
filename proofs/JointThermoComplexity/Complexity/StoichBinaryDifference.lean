module
public import proofs.JointThermoComplexity.Complexity.SignedBinaryDifference
public import proofs.JointThermoComplexity.Complexity.InputSize

set_option autoImplicit false
@[expose] public section

/-! The bitwise signed algorithm produces the exact literal stoichiometric coefficient, product minus reactant. -/

namespace JointThermoComplexity.Complexity.StoichBinaryDifference
open NetworkData

theorem code_eq {n : ℕ} (q : ReactionCircuit.Reaction n) (s : Fin n) :
    SignedBinaryDifference.code (q.product s).bits (q.reactant s).bits = BitCodec.integerCode (stoich q s) :=
  SignedBinaryDifference.naturals (q.product s) (q.reactant s)

theorem decoded_length (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) :
    (SignedBinaryDifference.code ((Q.network.reactions i).product s).bits ((Q.network.reactions i).reactant s).bits).length ≤
      input.length + 1 := by
  have hc := SignedBinaryDifference.code_length_le ((Q.network.reactions i).product s).bits ((Q.network.reactions i).reactant s).bits
  have hfields := InputSize.complex_entries_le_input Q i s
  have hlen : Q.code.length = input.length := by rw [NetworkCodec.decode_sound hd]
  simp only [BitCodec.naturalCode_length] at hfields
  omega

end JointThermoComplexity.Complexity.StoichBinaryDifference

#print axioms JointThermoComplexity.Complexity.StoichBinaryDifference.code_eq
#print axioms JointThermoComplexity.Complexity.StoichBinaryDifference.decoded_length
