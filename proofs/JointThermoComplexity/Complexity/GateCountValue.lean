module
public import proofs.JointThermoComplexity.Complexity.DecodedDimensions
public import proofs.JointThermoComplexity.Complexity.InputSize

set_option autoImplicit false
@[expose] public section

/-! The total gate-count value represented by the guarded parser/count machine. -/

namespace JointThermoComplexity.Complexity.GateCountValue

def count (input : List Bool) : ℕ :=
  match NetworkCodec.decode input with
  | none => 0
  | some Q => NetworkMembership.gates Q.network

theorem on_decode {input : List Bool} {Q : NetworkCodec.Input} (h : NetworkCodec.decode input = some Q) :
    count input = NetworkMembership.gates Q.network := by simp only [count, h]

theorem rejected_decode {input : List Bool} (h : NetworkInputControl.accepted input = false) :
    NetworkCodec.decode input = none := by
  cases hd : NetworkCodec.decode input with
  | none => rfl
  | some Q =>
    have ha := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    rw [h] at ha
    cases ha

theorem rejected {input : List Bool} (h : NetworkInputControl.accepted input = false) : count input = 0 := by
  simp only [count, rejected_decode h]

theorem code (Q : NetworkCodec.Input) : count Q.code = NetworkMembership.gates Q.network :=
  on_decode (NetworkCodec.decode_code Q)

theorem bound (input : List Bool) : count input ≤ 3 * input.length := by
  cases hd : NetworkCodec.decode input with
  | none => simp only [count, hd, Nat.zero_le]
  | some Q =>
    rw [on_decode hd, NetworkCodec.decode_sound hd]
    exact InputSize.gates_le_input_length Q

end JointThermoComplexity.Complexity.GateCountValue

#print axioms JointThermoComplexity.Complexity.GateCountValue.bound
