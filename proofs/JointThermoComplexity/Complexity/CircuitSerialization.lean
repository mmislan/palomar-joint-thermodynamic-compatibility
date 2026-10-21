module
public import proofs.JointThermoComplexity.Complexity.ExactGateCount
public import proofs.JointThermoComplexity.Complexity.RepeatedOutput

set_option autoImplicit false
@[expose] public section

/-!
# Forward serialization of circuit equations

The left-nested semantic conjunction can be emitted as counted conjunction tags,
then truth, then gate equations in their construction order. No reverse traversal
of a stored syntax tree is needed for that order.
-/

namespace JointThermoComplexity.Complexity.CircuitSerialization
open RealSyntax RealCircuit

variable {n k m r c : ℕ}

def conjunctionTag : List Bool := [true, false, false]

theorem copies_succ_left (word : List Bool) (v : ℕ) :
    RepeatedOutput.copies word (v + 1) = word ++ RepeatedOutput.copies word v := by
  induction v with
  | zero => simp [RepeatedOutput.copies]
  | succ v ih =>
    change RepeatedOutput.copies word (v + 1) ++ word = word ++ (RepeatedOutput.copies word v ++ word)
    rw [ih, List.append_assoc]

def equationStream : {k : ℕ} → Circuit n k → (Fin n → Fin m) → (Fin k → Fin m) → List Bool
  | _, .nil, _, _ => []
  | _, .snoc circuit step, inputs, outputs =>
      equationStream circuit inputs (fun i => outputs i.castSucc) ++
        (Formula.eq (.var (outputs (Fin.last _))) (step.term inputs (fun i => outputs i.castSucc))).code

theorem circuit_code (circuit : Circuit n k) (inputs : Fin n → Fin m) (outputs : Fin k → Fin m) :
    (circuit.formula inputs outputs).code = RepeatedOutput.copies conjunctionTag k ++
      [false, false, false] ++ equationStream circuit inputs outputs := by
  induction circuit generalizing m with
  | nil => rfl
  | snoc circuit step ih =>
    simp only [Circuit.formula, Formula.code, equationStream, copies_succ_left, ih,
      conjunctionTag, List.append_assoc]

theorem network_circuit_code (Q : NetworkData.Network n r c) :
    (NetworkMembership.circuitFormula Q).code =
      RepeatedOutput.copies conjunctionTag (NetworkMembership.gates Q) ++ [false, false, false] ++
        equationStream (NetworkCircuit.dense Q.reactions).circuit
          (NetworkMembership.activityIndex Q) (NetworkMembership.auxiliaryIndex Q) :=
  circuit_code _ _ _

end JointThermoComplexity.Complexity.CircuitSerialization

#print axioms JointThermoComplexity.Complexity.CircuitSerialization.network_circuit_code
