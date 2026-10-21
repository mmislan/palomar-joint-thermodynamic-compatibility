module
public import proofs.JointThermoComplexity.Complexity.GateStore
public import proofs.JointThermoComplexity.Complexity.TemplateRuntime

set_option autoImplicit false
@[expose] public section

/-! Charge gate emission, result-address overwrite and successor to the encoded input bound. -/

namespace JointThermoComplexity.Complexity.GateStoreRuntime

variable {w : ℕ}

theorem bound (values : Fin (w + 1) → ℕ) (old : ℕ) (target left right : Fin (w + 1)) (L : ℕ)
    (ht : values target ≤ 4 * L) (hl : values left ≤ 4 * L) (hr : values right ≤ 4 * L) (ho : old ≤ 4 * L) :
    GateStore.timeBound values old target left right ≤ 96 * L ^ 2 + 180 * L + 88 := by
  have hb := TemplateRuntime.binary_bound values target left right L ht hl hr
  unfold GateStore.timeBound
  omega

theorem decoded_bound {input : List Bool} {Q : NetworkCodec.Input}
    (h : NetworkCodec.decode input = some Q) (values : Fin (w + 1) → Fin (NetworkMembership.arity Q.network))
    (old : ℕ) (target left right : Fin (w + 1)) (ho : old ≤ 4 * input.length) :
    GateStore.timeBound (fun j => (values j).val) old target left right ≤
      96 * input.length ^ 2 + 180 * input.length + 88 :=
  bound _ _ _ _ _ _ (NetworkNumbering.decoded_index_bound h (values target)).le
    (NetworkNumbering.decoded_index_bound h (values left)).le
    (NetworkNumbering.decoded_index_bound h (values right)).le ho

end JointThermoComplexity.Complexity.GateStoreRuntime

#print axioms JointThermoComplexity.Complexity.GateStoreRuntime.decoded_bound
