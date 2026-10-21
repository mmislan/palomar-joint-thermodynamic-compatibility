module
public import proofs.JointThermoComplexity.Complexity.BinaryGateOutput
public import proofs.JointThermoComplexity.Complexity.UnaryGateOutput
public import proofs.JointThermoComplexity.Complexity.FixedGateOutput
public import proofs.JointThermoComplexity.Complexity.BinderOutput
public import proofs.JointThermoComplexity.Complexity.CircuitPrefixOutput
public import proofs.JointThermoComplexity.Complexity.CountSum

set_option autoImplicit false
@[expose] public section

/-! Actual template runtime bounds in the length of an accepted binary network input. -/

namespace JointThermoComplexity.Complexity.TemplateRuntime

variable {w : ℕ}

theorem variable_time_eq (v : ℕ) : VariableOutput.timeBound v = 2 * v ^ 2 + 12 * v + 18 := by
  unfold VariableOutput.timeBound ReusableIndexEmitter.timeBound
  ring1

theorem variable_bound {v L : ℕ} (h : v ≤ 4 * L) :
    VariableOutput.timeBound v ≤ 32 * L ^ 2 + 48 * L + 18 := by
  rw [variable_time_eq]
  calc
    2 * v ^ 2 + 12 * v + 18 ≤ 2 * (4 * L) ^ 2 + 12 * (4 * L) + 18 :=
      Nat.add_le_add_right (Nat.add_le_add
        (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h 2)) (Nat.mul_le_mul_left 12 h)) 18
    _ = 32 * L ^ 2 + 48 * L + 18 := by ring1

theorem binary_bound (values : Fin w → ℕ) (target left right : Fin w) (L : ℕ)
    (ht : values target ≤ 4 * L) (hl : values left ≤ 4 * L) (hr : values right ≤ 4 * L) :
    BinaryGateOutput.timeBound values target left right ≤ 96 * L ^ 2 + 144 * L + 65 := by
  have ha := variable_bound ht
  have hb := variable_bound hl
  have hc := variable_bound hr
  unfold BinaryGateOutput.timeBound
  omega

theorem unary_bound (values : Fin w → ℕ) (target source : Fin w) (L : ℕ)
    (ht : values target ≤ 4 * L) (hs : values source ≤ 4 * L) :
    UnaryGateOutput.timeBound values target source ≤ 64 * L ^ 2 + 96 * L + 46 := by
  have ha := variable_bound ht
  have hb := variable_bound hs
  unfold UnaryGateOutput.timeBound
  omega

theorem unit_bound {v L : ℕ} (h : v ≤ 4 * L) :
    VariableOutput.timeBound v + 13 ≤ 32 * L ^ 2 + 48 * L + 31 := by
  have hv := variable_bound h
  omega

theorem positive_bound {v L : ℕ} (h : v ≤ 4 * L) :
    VariableOutput.timeBound v + 11 ≤ 32 * L ^ 2 + 48 * L + 29 := by
  have hv := variable_bound h
  omega

theorem decoded_binary_bound {input : List Bool} {Q : NetworkCodec.Input}
    (h : NetworkCodec.decode input = some Q) (values : Fin w → Fin (NetworkMembership.arity Q.network))
    (target left right : Fin w) :
    BinaryGateOutput.timeBound (fun j => (values j).val) target left right ≤
      96 * input.length ^ 2 + 144 * input.length + 65 :=
  binary_bound _ _ _ _ _ (NetworkNumbering.decoded_index_bound h (values target)).le
    (NetworkNumbering.decoded_index_bound h (values left)).le
    (NetworkNumbering.decoded_index_bound h (values right)).le

theorem decoded_binder_bound {input : List Bool} {Q : NetworkCodec.Input}
    (h : NetworkCodec.decode input = some Q) : 4 * NetworkMembership.arity Q.network + 4 ≤ 16 * input.length + 4 := by
  have ha := NetworkNumbering.decoded_arity_bound h
  omega

theorem decoded_circuit_prefix_bound {input : List Bool} {Q : NetworkCodec.Input}
    (h : NetworkCodec.decode input = some Q) : 6 * NetworkMembership.gates Q.network + 6 ≤ 18 * input.length + 6 := by
  have hg : NetworkMembership.gates Q.network ≤ 3 * input.length := by
    rw [NetworkCodec.decode_sound h]
    exact InputSize.gates_le_input_length Q
  omega

end JointThermoComplexity.Complexity.TemplateRuntime

#print axioms JointThermoComplexity.Complexity.TemplateRuntime.decoded_binary_bound
