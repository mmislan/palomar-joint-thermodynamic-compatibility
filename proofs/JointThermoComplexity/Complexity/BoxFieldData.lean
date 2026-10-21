module
public import proofs.JointThermoComplexity.Complexity.InputSize

set_option autoImplicit false
@[expose] public section

/-! Literal rational-box field order and binary-length bounds without rational normalization. -/

namespace JointThermoComplexity.Complexity.BoxFieldData
open NetworkData FiniteCodec

theorem box_code (b : ClosedBox) :
    DataCodec.box.code b = BitCodec.integerCode b.lower.numerator ++
      (BitCodec.naturalCode b.lower.denominator ++ (BitCodec.integerCode b.upper.numerator ++
        BitCodec.naturalCode b.upper.denominator)) := by
  change (BitCodec.integerCode b.lower.numerator ++ BitCodec.naturalCode b.lower.denominator) ++
    (BitCodec.integerCode b.upper.numerator ++ BitCodec.naturalCode b.upper.denominator) = _
  rw [List.append_assoc]

theorem box_length_le_input (Q : NetworkCodec.Input) (s : Fin Q.speciesCount) (b : ClosedBox)
    (hbox : Q.network.boxes s = some b) : (DataCodec.box.code b).length ≤ Q.code.length := by
  have he := InputSize.functionCode_entry_le (optional DataCodec.box) Q.network.boxes s
  have hb := InputSize.body_length_le Q
  rw [InputSize.network_code_length] at hb
  rw [hbox] at he
  change (true :: DataCodec.box.code b).length ≤ _ at he
  simp only [List.length_cons] at he
  omega

theorem fields_le_input (Q : NetworkCodec.Input) (s : Fin Q.speciesCount) (b : ClosedBox)
    (hbox : Q.network.boxes s = some b) :
    (BitCodec.integerCode b.lower.numerator).length ≤ Q.code.length ∧
    (BitCodec.naturalCode b.lower.denominator).length ≤ Q.code.length ∧
    (BitCodec.integerCode b.upper.numerator).length ≤ Q.code.length ∧
    (BitCodec.naturalCode b.upper.denominator).length ≤ Q.code.length := by
  have hb := box_length_le_input Q s b hbox
  rw [box_code] at hb
  simp only [List.length_append] at hb
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem decoded_fields_le_input (input : List Bool) (Q : NetworkCodec.Input)
    (hd : NetworkCodec.decode input = some Q) (s : Fin Q.speciesCount) (b : ClosedBox)
    (hbox : Q.network.boxes s = some b) :
    (BitCodec.integerCode b.lower.numerator).length ≤ input.length ∧
    (BitCodec.naturalCode b.lower.denominator).length ≤ input.length ∧
    (BitCodec.integerCode b.upper.numerator).length ≤ input.length ∧
    (BitCodec.naturalCode b.upper.denominator).length ≤ input.length := by
  rw [NetworkCodec.decode_sound hd]
  exact fields_le_input Q s b hbox

end JointThermoComplexity.Complexity.BoxFieldData

#print axioms JointThermoComplexity.Complexity.BoxFieldData.box_code
#print axioms JointThermoComplexity.Complexity.BoxFieldData.decoded_fields_le_input
