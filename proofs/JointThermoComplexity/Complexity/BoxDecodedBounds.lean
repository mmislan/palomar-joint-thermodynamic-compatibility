module
public import proofs.JointThermoComplexity.Complexity.BoxOptionalRuntime
public import proofs.JointThermoComplexity.Complexity.BoxFieldData
public import proofs.JointThermoComplexity.Complexity.DecodedDimensions

set_option autoImplicit false
@[expose] public section

/-! Decoded networks supply all box-field lengths, species fuel and finite activity-index bounds. -/

namespace JointThermoComplexity.Complexity.BoxDecodedBounds

theorem bounded (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (s : Fin Q.speciesCount) : BoxOptionalRuntime.Bounded input.length (Q.network.boxes s) := by
  cases hb : Q.network.boxes s with
  | none => trivial
  | some b => exact BoxFieldData.decoded_fields_le_input input Q hd s b hb

theorem arity (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q) :
    NetworkMembership.arity Q.network ≤ 4 * input.length := by
  rw [NetworkCodec.decode_sound hd]
  exact InputSize.arity_le_input_length Q

theorem species (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q) :
    Q.speciesCount ≤ input.length := by
  have hdims := DecodedDimensions.decode_counts hd
  have h := DimensionHeaders.count_sum_bound input
  rw [hdims.1, hdims.2.1, hdims.2.2] at h
  omega

theorem index_value (Q : NetworkCodec.Input) (s : Fin Q.speciesCount) :
    (NetworkMembership.activityIndex Q.network s).val = s.val := rfl

end JointThermoComplexity.Complexity.BoxDecodedBounds

#print axioms JointThermoComplexity.Complexity.BoxDecodedBounds.bounded
