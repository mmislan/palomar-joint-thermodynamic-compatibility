module
public import proofs.JointThermoComplexity.Complexity.BooleanMask
public import proofs.JointThermoComplexity.Complexity.DataCodec

set_option autoImplicit false
@[expose] public section

/-! The checked mask machine's status and copied data are literal motif codecs. -/

namespace JointThermoComplexity.Complexity.MaskCodecBridge
open _root_.Complexity
open FiniteCodec

variable {α β : Type}

theorem transport_parse_iff (A : Codec α) (e : α ≃ β) (input : List Bool) :
    (∃ b tail, (DataCodec.transport A e).parse input = some (b, tail)) ↔
      ∃ a tail, A.parse input = some (a, tail) := by
  cases hp : A.parse input with
  | none => simp [DataCodec.transport, hp]
  | some pair =>
    obtain ⟨a, tail⟩ := pair
    simp [DataCodec.transport, hp]

theorem finset_status_iff (v : ℕ) (input : List Bool) :
    BooleanVector.accepted v input = true ↔ ∃ s tail, (DataCodec.finset v).parse input = some (s, tail) := by
  change BooleanVector.accepted v input = true ↔
    ∃ s tail, (DataCodec.transport (finiteFunction boolean v) (DataCodec.finsetEquiv v)).parse input = some (s, tail)
  rw [transport_parse_iff]
  exact BooleanVector.status_iff v input

theorem finset_code_length {v : ℕ} (s : Finset (Fin v)) : ((DataCodec.finset v).code s).length = v := by
  change ((finiteFunction boolean v).code ((DataCodec.finsetEquiv v).symm s)).length = v
  exact BooleanVector.code_length _

theorem finset_parsed_prefix {v : ℕ} {input tail : List Bool} {s : Finset (Fin v)}
    (h : (DataCodec.finset v).parse input = some (s, tail)) :
    (DataCodec.finset v).code s = input.take v ∧ tail = input.drop v := by
  rw [(DataCodec.finset v).sound h]
  exact ⟨(List.take_left' (finset_code_length s)).symm, (List.drop_left' (finset_code_length s)).symm⟩

theorem machine_status_iff (v : ℕ) (input : List Bool) {value : Γ}
    (h : value = Γ.ofBool (BooleanVector.accepted v input)) :
    value = Γ.one ↔ ∃ s tail, (DataCodec.finset v).parse input = some (s, tail) := by
  rw [h, ← finset_status_iff]
  cases BooleanVector.accepted v input <;> simp [Γ.ofBool]

end JointThermoComplexity.Complexity.MaskCodecBridge

#print axioms JointThermoComplexity.Complexity.MaskCodecBridge.machine_status_iff
#print axioms JointThermoComplexity.Complexity.MaskCodecBridge.finset_parsed_prefix
