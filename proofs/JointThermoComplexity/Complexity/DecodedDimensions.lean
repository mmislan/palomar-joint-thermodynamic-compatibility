module
public import proofs.JointThermoComplexity.Complexity.NetworkInputControl

set_option autoImplicit false
@[expose] public section

/-! Connect retained dimension counts and acceptance to the exact canonical decoded input. -/

namespace JointThermoComplexity.Complexity.DecodedDimensions

theorem code_counts (Q : NetworkCodec.Input) :
    DimensionHeaders.species Q.code = Q.speciesCount ∧
    DimensionHeaders.reactions Q.code = Q.reactionCount ∧
    DimensionHeaders.cores Q.code = Q.coreCount := by
  simp only [DimensionHeaders.species, DimensionHeaders.reactions, DimensionHeaders.cores,
    DimensionHeaders.tail₁, DimensionHeaders.tail₂, NetworkCodec.Input.code, List.append_assoc,
    HeaderControl.suffix_code, HeaderControl.count_code, and_self]

theorem decode_counts {input : List Bool} {Q : NetworkCodec.Input} (h : NetworkCodec.decode input = some Q) :
    DimensionHeaders.species input = Q.speciesCount ∧
    DimensionHeaders.reactions input = Q.reactionCount ∧
    DimensionHeaders.cores input = Q.coreCount := by
  rw [NetworkCodec.decode_sound h]
  exact code_counts Q

theorem accepted_canonical {input : List Bool} (h : NetworkInputControl.accepted input = true) :
    ∃ Q, NetworkCodec.decode input = some Q ∧ input = Q.code ∧
      DimensionHeaders.species input = Q.speciesCount ∧
      DimensionHeaders.reactions input = Q.reactionCount ∧ DimensionHeaders.cores input = Q.coreCount := by
  obtain ⟨Q, hQ⟩ := (NetworkInputControl.status_iff_decode input).mp h
  exact ⟨Q, hQ, NetworkCodec.decode_sound hQ, decode_counts hQ⟩

theorem copied_length_le (input : List Bool) : (NetworkInputControl.copied input).length ≤ input.length := by
  have h := congrArg List.length (NetworkInputControl.consumed_split input)
  simp only [List.length_append] at h
  omega

end JointThermoComplexity.Complexity.DecodedDimensions

#print axioms JointThermoComplexity.Complexity.DecodedDimensions.accepted_canonical
