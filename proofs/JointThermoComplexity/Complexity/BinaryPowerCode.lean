module
public import proofs.JointThermoComplexity.Complexity.CircuitSerialization

set_option autoImplicit false
@[expose] public section

/-! Exact forward equation-stream extensions for the two repeated-squaring bit cases. -/

namespace JointThermoComplexity.Complexity.BinaryPowerCode
open RealSyntax RealCircuit CircuitSerialization

variable {n arity : ℕ}

def multiply (target left right : Fin arity) : List Bool :=
  (Formula.eq (.var target) (.mul (.var left) (.var right))).code

theorem advance_false (s : BinaryPower.State n) (inputs : Fin n → Fin arity) (outputs : Fin (s.size + 1) → Fin arity) :
    equationStream (s.advance false).circuit inputs outputs =
      equationStream s.circuit inputs (fun i => outputs i.castSucc) ++
        multiply (outputs (Fin.last s.size)) (outputs s.power.castSucc) (outputs s.power.castSucc) := rfl

theorem advance_true (s : BinaryPower.State n) (inputs : Fin n → Fin arity) (outputs : Fin (s.size + 2) → Fin arity) :
    equationStream (s.advance true).circuit inputs outputs =
      (equationStream s.circuit inputs (fun i => outputs i.castSucc.castSucc) ++
        multiply (outputs (Fin.last s.size).castSucc) (outputs s.accumulator.castSucc.castSucc) (outputs s.power.castSucc.castSucc)) ++
        multiply (outputs (Fin.last (s.size + 1))) (outputs s.power.castSucc.castSucc) (outputs s.power.castSucc.castSucc) := rfl

end JointThermoComplexity.Complexity.BinaryPowerCode

#print axioms JointThermoComplexity.Complexity.BinaryPowerCode.advance_true
