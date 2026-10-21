module
public import proofs.JointThermoComplexity.Complexity.PowerTrueBlock
public import proofs.JointThermoComplexity.Complexity.GateStoreRuntime

set_option autoImplicit false
@[expose] public section

/-! Actual polynomial transition bounds for both fixed repeated-squaring bit blocks. -/

namespace JointThermoComplexity.Complexity.PowerBlockRuntime
open PowerPorts

variable {arity : ℕ}

theorem false_bound (m : ℕ) (values : Fin (m + 13) → Fin arity) (L : ℕ) (ha : arity ≤ 4 * L) :
    PowerFalseBlock.timeBound m values ≤ 96 * L ^ 2 + 180 * L + 88 := by
  have hval : ∀ j, (values j).val ≤ 4 * L := fun j => (values j).isLt.le.trans ha
  exact GateStoreRuntime.bound (fun j => (values j).val) (values (power m)).val
    (next m) (power m) (power m) L (hval _) (hval _) (hval _) (hval _)

theorem true_bound (m : ℕ) (values : Fin (m + 13) → Fin arity) (room : (values (next m)).val + 1 < arity)
    (L : ℕ) (ha : arity ≤ 4 * L) : PowerTrueBlock.timeBound m values room ≤ 192 * L ^ 2 + 360 * L + 177 := by
  have hval : ∀ j, (values j).val ≤ 4 * L := fun j => (values j).isLt.le.trans ha
  have hfirst := GateStoreRuntime.bound (fun j => (values j).val) (values (accumulator m)).val
    (next m) (accumulator m) (power m) L (hval _) (hval _) (hval _) (hval _)
  have hsecond := false_bound m (PowerTrueValues.afterFirst m values room) L ha
  unfold PowerTrueBlock.timeBound
  omega

theorem decoded_false_bound (m : ℕ) {input : List Bool} {Q : NetworkCodec.Input}
    (h : NetworkCodec.decode input = some Q) (values : Fin (m + 13) → Fin (NetworkMembership.arity Q.network)) :
    PowerFalseBlock.timeBound m values ≤ 96 * input.length ^ 2 + 180 * input.length + 88 :=
  false_bound m values input.length (NetworkNumbering.decoded_arity_bound h)

theorem decoded_true_bound (m : ℕ) {input : List Bool} {Q : NetworkCodec.Input}
    (h : NetworkCodec.decode input = some Q) (values : Fin (m + 13) → Fin (NetworkMembership.arity Q.network))
    (room : (values (next m)).val + 1 < NetworkMembership.arity Q.network) :
    PowerTrueBlock.timeBound m values room ≤ 192 * input.length ^ 2 + 360 * input.length + 177 :=
  true_bound m values room input.length (NetworkNumbering.decoded_arity_bound h)

end JointThermoComplexity.Complexity.PowerBlockRuntime

#print axioms JointThermoComplexity.Complexity.PowerBlockRuntime.decoded_false_bound
#print axioms JointThermoComplexity.Complexity.PowerBlockRuntime.decoded_true_bound
