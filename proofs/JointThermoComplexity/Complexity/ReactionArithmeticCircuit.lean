module
public import proofs.JointThermoComplexity.Complexity.CircuitGateCode
public import proofs.JointThermoComplexity.Complexity.ReactionArithmetic

set_option autoImplicit false
@[expose] public section

/-! Identify the actual four-gate word with the literal reaction arithmetic circuit. -/

namespace JointThermoComplexity.Complexity.ReactionArithmeticCircuit
open RealCircuit CircuitSerialization PowerAddressCircuit

def build {n k : ℕ} (c : Circuit n k) (lhs rhs : Fin k) (num : ℕ) : Circuit n (k + 4) :=
  let negative := c.snoc (.neg rhs)
  let difference := negative.snoc (.add lhs.castSucc (Fin.last k))
  let coefficient := difference.snoc (.constant (num : ℤ))
  coefficient.snoc (.mul (Fin.last (k + 1)).castSucc (Fin.last (k + 2)))

theorem stream {n k : ℕ} (offset arity : ℕ) (c : Circuit n k) (lhs rhs : Fin k) (num : ℕ)
    (inputs : Fin n → Fin arity) (h : offset + (k + 4) ≤ arity) :
    equationStream (build c lhs rhs num) inputs (index offset _ arity h) =
      equationStream c inputs (index offset k arity (by omega)) ++
        ReactionArithmetic.word (⟨offset + k, by omega⟩ : Fin arity)
          ⟨offset + rhs.val, by have hi := rhs.isLt; omega⟩
          ⟨offset + lhs.val, by have hi := lhs.isLt; omega⟩ num (by change offset + k + 3 < arity; omega) := by
  let negative := c.snoc (.neg rhs)
  let difference := negative.snoc (.add lhs.castSucc (Fin.last k))
  let coefficient := difference.snoc (.constant (num : ℤ))
  have hn := CircuitGateCode.snoc_stream offset arity c (.neg rhs) inputs (by omega : offset + (k + 1) ≤ arity)
  have hd := CircuitGateCode.snoc_stream offset arity negative (.add lhs.castSucc (Fin.last k)) inputs
    (by omega : offset + (k + 2) ≤ arity)
  have hc := CircuitGateCode.snoc_stream offset arity difference (.constant (num : ℤ)) inputs
    (by omega : offset + (k + 3) ≤ arity)
  have hm := CircuitGateCode.snoc_stream offset arity coefficient
    (.mul (Fin.last (k + 1)).castSucc (Fin.last (k + 2))) inputs h
  apply hm.trans
  rw [hc, hd, hn]
  simp only [Step.term, ReactionArithmetic.word, ReactionDifference.word, BinaryPowerCode.multiply, index, Fin.val_last,
    Fin.val_castSucc, Nat.add_assoc, List.append_assoc]

end JointThermoComplexity.Complexity.ReactionArithmeticCircuit

#print axioms JointThermoComplexity.Complexity.ReactionArithmeticCircuit.stream
