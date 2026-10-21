module
public import proofs.JointThermoComplexity.Complexity.InputSize

set_option autoImplicit false
@[expose] public section

/-! Natural variable addresses used by the executable formula generator. -/

namespace JointThermoComplexity.Complexity.NetworkNumbering
open NetworkData NetworkMembership

variable {n r c : ℕ}

@[simp] theorem activity_value (Q : Network n r c) (s : Fin n) :
    (activityIndex Q s).val = s.val := rfl

@[simp] theorem current_value (Q : Network n r c) (i : Fin r) :
    (currentIndex Q i).val = n + i.val := rfl

@[simp] theorem auxiliary_value (Q : Network n r c) (g : Fin (gates Q)) :
    (auxiliaryIndex Q g).val = (n + r) + g.val := rfl

theorem activity_before_current (Q : Network n r c) (s : Fin n) (i : Fin r) :
    (activityIndex Q s).val < (currentIndex Q i).val := by
  simp only [activity_value, current_value]
  omega

theorem current_before_auxiliary (Q : Network n r c) (i : Fin r) (g : Fin (gates Q)) :
    (currentIndex Q i).val < (auxiliaryIndex Q g).val := by
  simp only [current_value, auxiliary_value]
  omega

theorem auxiliary_order (Q : Network n r c) (g h : Fin (gates Q)) (hgh : g.val < h.val) :
    (auxiliaryIndex Q g).val < (auxiliaryIndex Q h).val := by
  simp only [auxiliary_value]
  omega

theorem decoded_arity_bound {input : List Bool} {Q : NetworkCodec.Input}
    (h : NetworkCodec.decode input = some Q) : arity Q.network ≤ 4 * input.length := by
  rw [NetworkCodec.decode_sound h]
  exact InputSize.arity_le_input_length Q

theorem decoded_index_bound {input : List Bool} {Q : NetworkCodec.Input}
    (h : NetworkCodec.decode input = some Q) (idx : Fin (arity Q.network)) : idx.val < 4 * input.length :=
  idx.isLt.trans_le (decoded_arity_bound h)

end JointThermoComplexity.Complexity.NetworkNumbering

#print axioms JointThermoComplexity.Complexity.NetworkNumbering.decoded_index_bound
