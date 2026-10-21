module
public import proofs.JointThermoComplexity.Complexity.PowerAddressCircuit

set_option autoImplicit false
@[expose] public section

/-! A unit gate starts a monomial even when its preceding circuit has no gates. -/

namespace JointThermoComplexity.Complexity.UnitCircuitCode
open RealCircuit RealSyntax CircuitSerialization PowerAddressCircuit

theorem snoc_stream {n k : ℕ} (offset arity : ℕ) (c : Circuit n k)
    (inputs : Fin n → Fin arity) (h : offset + (k + 1) ≤ arity) :
    equationStream (c.snoc (.constant 1)) inputs (index offset _ arity h) =
      equationStream c inputs (index offset k arity (by omega)) ++
        (Formula.eq (.var (⟨offset + k, by omega⟩ : Fin arity)) (.int 1)).code := by
  have hi : (fun i : Fin k => index offset (k + 1) arity h i.castSucc) =
      index offset k arity (by omega) := by funext i; apply Fin.ext; rfl
  change equationStream c inputs (fun i => index offset (k + 1) arity h i.castSucc) ++
    (Formula.eq (.var (index offset (k + 1) arity h (Fin.last k))) (.int 1)).code = _
  rw [hi]
  rfl

end JointThermoComplexity.Complexity.UnitCircuitCode

#print axioms JointThermoComplexity.Complexity.UnitCircuitCode.snoc_stream
