module
public import proofs.JointThermoComplexity.Complexity.ReactionArrayData
public import proofs.JointThermoComplexity.Complexity.DimensionSkip

set_option autoImplicit false
@[expose] public section

/-! Split canonical network input into dimensions, reaction records and the unused suffix. -/

namespace JointThermoComplexity.Complexity.NetworkTallyData
open FiniteCodec

def reactions (Q : NetworkCodec.Input) : List (ReactionCircuit.Reaction Q.speciesCount) := List.ofFn Q.network.reactions

def headers (Q : NetworkCodec.Input) : List Bool := DimensionSkip.code Q.speciesCount Q.reactionCount Q.coreCount

def tail (Q : NetworkCodec.Input) : List Bool :=
  (finiteFunction (DataCodec.motif Q.speciesCount Q.reactionCount) Q.coreCount).code Q.network.motifs ++
    (finiteFunction boolean Q.reactionCount).code Q.network.forward ++
    (finiteFunction (optional DataCodec.box) Q.speciesCount).code Q.network.boxes

theorem code_split (Q : NetworkCodec.Input) :
    Q.code = headers Q ++ (ReactionArrayData.code (reactions Q) ++ tail Q) := by
  have hnetwork : (DataCodec.network Q.speciesCount Q.reactionCount Q.coreCount).code Q.network =
      ReactionArrayData.code (reactions Q) ++ tail Q := by
    change ((finiteFunction (DataCodec.reaction Q.speciesCount) Q.reactionCount).code Q.network.reactions ++
      (finiteFunction (DataCodec.motif Q.speciesCount Q.reactionCount) Q.coreCount).code Q.network.motifs) ++
      ((finiteFunction boolean Q.reactionCount).code Q.network.forward ++
      (finiteFunction (optional DataCodec.box) Q.speciesCount).code Q.network.boxes) = _
    rw [ReactionArrayData.finiteFunction_code]
    simp only [reactions, tail, List.append_assoc]
  rw [NetworkCodec.Input.code, hnetwork]
  simp only [headers, DimensionSkip.code, List.append_assoc]

theorem reaction_count (Q : NetworkCodec.Input) : (reactions Q).length = Q.reactionCount := by
  simp only [reactions, List.length_ofFn]

theorem gate_count (Q : NetworkCodec.Input) :
    ExactGateCount.networkCost (reactions Q) = NetworkMembership.gates Q.network :=
  (ExactGateCount.gates_eq_cost Q.network).symm

theorem prefix_length_le (Q : NetworkCodec.Input) :
    (headers Q ++ ReactionArrayData.code (reactions Q)).length ≤ Q.code.length := by
  rw [code_split]
  simp only [List.length_append]
  omega

end JointThermoComplexity.Complexity.NetworkTallyData

#print axioms JointThermoComplexity.Complexity.NetworkTallyData.code_split
