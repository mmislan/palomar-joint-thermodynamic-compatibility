module
public import proofs.JointThermoComplexity.Complexity.GateCountValue

set_option autoImplicit false
@[expose] public section

/-! The bounded binder count computed from retained dimensions and the exact gate count. -/

namespace JointThermoComplexity.Complexity.ArityValue

def offset (input : List Bool) : ℕ := DimensionHeaders.species input + DimensionHeaders.reactions input
def arity (input : List Bool) : ℕ := offset input + GateCountValue.count input

theorem on_decode {input : List Bool} {Q : NetworkCodec.Input} (h : NetworkCodec.decode input = some Q) :
    arity input = NetworkMembership.arity Q.network := by
  obtain ⟨hs, hr, _⟩ := DecodedDimensions.decode_counts h
  simp only [arity, offset, hs, hr, GateCountValue.on_decode h, NetworkMembership.arity]

theorem offset_bound (input : List Bool) : offset input ≤ input.length := by
  have hd := DimensionHeaders.count_sum_bound input
  unfold offset
  omega

theorem arity_bound (input : List Bool) : arity input ≤ 4 * input.length := by
  have hd := offset_bound input
  have hg := GateCountValue.bound input
  unfold arity
  omega

end JointThermoComplexity.Complexity.ArityValue

#print axioms JointThermoComplexity.Complexity.ArityValue.on_decode
