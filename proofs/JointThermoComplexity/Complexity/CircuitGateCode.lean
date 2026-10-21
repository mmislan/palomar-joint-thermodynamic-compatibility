module
public import proofs.JointThermoComplexity.Complexity.PowerAddressCircuit

set_option autoImplicit false
@[expose] public section

/-! Exact contiguous-address serialization for one arbitrary arithmetic gate. -/

namespace JointThermoComplexity.Complexity.CircuitGateCode
open RealCircuit RealSyntax CircuitSerialization PowerAddressCircuit

theorem snoc_stream {n k : ℕ} (offset arity : ℕ) (c : Circuit n k) (step : Step n k)
    (inputs : Fin n → Fin arity) (h : offset + (k + 1) ≤ arity) :
    equationStream (c.snoc step) inputs (index offset _ arity h) =
      equationStream c inputs (index offset k arity (by omega)) ++
        (Formula.eq (.var (⟨offset + k, by omega⟩ : Fin arity))
          (step.term inputs (index offset k arity (by omega)))).code := by
  have hi : (fun i : Fin k => index offset (k + 1) arity h i.castSucc) =
      index offset k arity (by omega) := by funext i; apply Fin.ext; rfl
  change equationStream c inputs (fun i => index offset (k + 1) arity h i.castSucc) ++
    (Formula.eq (.var (index offset (k + 1) arity h (Fin.last k)))
      (step.term inputs (fun i => index offset (k + 1) arity h i.castSucc))).code = _
  rw [hi]
  rfl

end JointThermoComplexity.Complexity.CircuitGateCode

#print axioms JointThermoComplexity.Complexity.CircuitGateCode.snoc_stream
