module
public import proofs.JointThermoComplexity.Complexity.ReactionArithmeticCircuit
public import proofs.JointThermoComplexity.Complexity.ReactionMonomials
public import proofs.JointThermoComplexity.Complexity.DataCodec

set_option autoImplicit false
@[expose] public section

/-! Exact identities linking the record-driven pieces to the existing literal reaction circuit and codec. -/

namespace JointThermoComplexity.Complexity.ReactionBuildCode
open RealCircuit CircuitSerialization PowerAddressCircuit ReactionMonomials

variable {n k : ℕ}

def lhs (c : Circuit n k) (q : ReactionCircuit.Reaction n) : Fin (right c q.reactant q.product).size :=
  Fin.castLE (MonomialCircuit.build_size_ge (left c q.reactant).circuit (MonomialCircuit.denseTerms q.product))
    (left c q.reactant).accumulator

theorem lhs_value (c : Circuit n k) (q : ReactionCircuit.Reaction n) :
    (lhs c q).val = (left c q.reactant).accumulator.val := rfl

theorem size (c : Circuit n k) (q : ReactionCircuit.Reaction n) :
    (ReactionCircuit.build c q).size = (right c q.reactant q.product).size + 4 := rfl

theorem output_value (c : Circuit n k) (q : ReactionCircuit.Reaction n) :
    (ReactionCircuit.build c q).output.val = (right c q.reactant q.product).size + 3 := rfl

theorem build_eq (c : Circuit n k) (q : ReactionCircuit.Reaction n) :
    (ReactionCircuit.build c q).circuit = ReactionArithmeticCircuit.build (right c q.reactant q.product).circuit
      (lhs c q) (right c q.reactant q.product).accumulator q.numerator := rfl

theorem record_code (q : ReactionCircuit.Reaction n) :
    (DataCodec.reaction n).code q =
      (FiniteCodec.functionCode FiniteCodec.natural q.reactant ++ FiniteCodec.functionCode FiniteCodec.natural q.product) ++
        (BitCodec.naturalCode q.numerator ++ BitCodec.naturalCode q.denominator) := rfl

theorem stream (offset arity : ℕ) (c : Circuit n k) (q : ReactionCircuit.Reaction n)
    (inputs : Fin n → Fin arity) (h : offset + (ReactionCircuit.build c q).size ≤ arity) :
    equationStream (ReactionCircuit.build c q).circuit inputs (index offset _ arity h) =
      equationStream (right c q.reactant q.product).circuit inputs
        (index offset _ arity (by rw [size] at h; omega)) ++
        ReactionArithmetic.word (⟨offset + (right c q.reactant q.product).size, by rw [size] at h; omega⟩ : Fin arity)
          ⟨offset + (right c q.reactant q.product).accumulator.val, by
            have hi := (right c q.reactant q.product).accumulator.isLt; rw [size] at h; omega⟩
          ⟨offset + (left c q.reactant).accumulator.val, by
            have hi := (left c q.reactant).accumulator.isLt
            have hs := MonomialCircuit.build_size_ge (left c q.reactant).circuit (MonomialCircuit.denseTerms q.product)
            change (left c q.reactant).size ≤ (right c q.reactant q.product).size at hs
            rw [size] at h; omega⟩ q.numerator
            (by change offset + (right c q.reactant q.product).size + 3 < arity; rw [size] at h; omega) :=
  ReactionArithmeticCircuit.stream offset arity (right c q.reactant q.product).circuit (lhs c q)
    (right c q.reactant q.product).accumulator q.numerator inputs h

end JointThermoComplexity.Complexity.ReactionBuildCode

#print axioms JointThermoComplexity.Complexity.ReactionBuildCode.stream
