module
public import proofs.JointThermoComplexity.Complexity.PowerUnit
public import proofs.JointThermoComplexity.Complexity.PowerAddressCircuit

set_option autoImplicit false
@[expose] public section

/-! Exact address and serialization identities for the unit that starts a power circuit. -/

namespace JointThermoComplexity.Complexity.PowerStartCircuit
open RealCircuit RealSyntax CircuitSerialization PowerAddressCircuit

variable {n k : ℕ}

def beforeState (offset old : ℕ) (_c : Circuit n k) (base : Fin k) : PowerAddressState.State :=
  ⟨offset + k, old, offset + base.val⟩

theorem unit_eq (offset old : ℕ) (c : Circuit n k) (base : Fin k) :
    PowerUnit.unitState (beforeState offset old c base) = ofState offset (BinaryPower.start c base) := by
  simp only [PowerUnit.unitState, beforeState, ofState, BinaryPower.start, Fin.val_last,
    Fin.val_castSucc, Nat.add_assoc]

theorem start_stream (offset arity : ℕ) (c : Circuit n k) (base : Fin k)
    (inputs : Fin n → Fin arity) (h : offset + (k + 1) ≤ arity) :
    equationStream (BinaryPower.start c base).circuit inputs (index offset _ arity h) =
      equationStream c inputs (index offset k arity (by omega)) ++
        (Formula.eq (.var (⟨offset + k, by omega⟩ : Fin arity)) (.int 1)).code := by
  have hi : (fun i : Fin k => index offset (k + 1) arity h i.castSucc) =
      index offset k arity (by omega) := by funext i; apply Fin.ext; rfl
  change equationStream c inputs (fun i => index offset (k + 1) arity h i.castSucc) ++
    (Formula.eq (.var (index offset (k + 1) arity h (Fin.last k))) (.int 1)).code = _
  rw [hi]
  rfl

end JointThermoComplexity.Complexity.PowerStartCircuit

#print axioms JointThermoComplexity.Complexity.PowerStartCircuit.start_stream
