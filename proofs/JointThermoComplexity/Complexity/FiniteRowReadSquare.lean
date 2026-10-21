module
public import proofs.JointThermoComplexity.Complexity.RowReadSquareMachine
public import proofs.JointThermoComplexity.Complexity.FiniteRowSquare
public import proofs.JointThermoComplexity.Complexity.FiniteStrictBounds

set_option autoImplicit false
@[expose] public section

/-! On the source promise, the composed machine reads one actual finite row
and emits its exact contribution to the finite strict energy polynomial.
-/

namespace JointThermoComplexity.Complexity.FiniteRowReadSquare
open _root_.Complexity EquationSystemCodec FiniteStrictData SparseInteger
open FiniteRowSquare
variable {w : ℕ}

theorem coefficient_bound (p : Data) (hp : FiniteEquationHardness.Domain p) (i : OriginalIndices p) :
    ∀ a ∈ original p i, a.1.natAbs ≤ 5 := by
  intro a ha
  exact (rawWeight_member _ a ha).trans (FiniteStrictBounds.original_weight p hp i)

theorem input_code (p : Data) (i : OriginalIndices p) :
    EquationRowControl.code (inputRow p i) = (SparsePolynomialCodec.polynomial p.arity).code (original p i) :=
  EquationRowMachine.code_finite p.arity (original p i)

theorem encoded_hoareTime (ports : RowSquareFrame.Ports w) (p : Data) (hp : FiniteEquationHardness.Domain p)
    (i : OriginalIndices p) (s : EquationRowControl.State) (suffix emitted : List Bool) (B W : ℕ)
    (hB : 2 ≤ B) (hlen : ((SparsePolynomialCodec.polynomial p.arity).code (original p i) ++ suffix).length ≤ B)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : RowReadSquareMachine.Stable ports R) :
    (RowReadSquareMachine.machine ports).HoareTime
      (RowSquareFrame.Logical ports
        { s with input := (SparsePolynomialCodec.polynomial p.arity).code (original p i) ++ suffix }
        (p.arity + scaleCount p).bits B W emitted R)
      (RowSquareFrame.Logical ports (EquationRowControl.expected s (inputRow p i) suffix)
        (p.arity + scaleCount p).bits B W (emitted ++ finiteEntries (contribution p i)) R)
      (RowReadSquareMachine.timeBound B W) := by
  have hr := FiniteStrictBounds.original_length p hp i
  have hc := coefficient_bound p hp i
  have hlen' : (EquationRowControl.code (inputRow p i) ++ suffix).length ≤ B := by
    simpa only [input_code] using hlen
  have h := RowReadSquareMachine.encoded_hoareTime ports s (inputRow p i) suffix
    (p.arity + scaleCount p).bits emitted B W hB hlen'
    (by simpa only [input_length] using hr) (input_bound p i hc) R hR
  simpa only [input_code, output_code p i s suffix hr hc] using h

theorem encoded_energy_hoareTime (ports : RowSquareFrame.Ports w) (p : Data) (hp : FiniteEquationHardness.Domain p)
    (i : OriginalIndices p) (s : EquationRowControl.State) (suffix emitted : List Bool) (B W : ℕ)
    (hB : 2 ≤ B) (hlen : ((SparsePolynomialCodec.polynomial p.arity).code (original p i) ++ suffix).length ≤ B)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : RowReadSquareMachine.Stable ports R) :
    (RowReadSquareMachine.machine ports).HoareTime
      (RowSquareFrame.Logical ports
        { s with input := (SparsePolynomialCodec.polynomial p.arity).code (original p i) ++ suffix }
        (p.arity + scaleCount p).bits B W emitted R)
      (RowSquareFrame.Logical ports (EquationRowControl.expected s (inputRow p i) suffix)
        (p.arity + scaleCount p).bits B W
        (emitted ++ finiteEntries (relabel (variableEnumeration p)
          (neg (scale 256 (relabel Sum.inl (square (energyFamily p (FiniteStrictNumbering.originalIndex p i)))))))) R)
      (RowReadSquareMachine.timeBound B W) := by
  simpa only [contribution_literal] using encoded_hoareTime ports p hp i s suffix emitted B W hB hlen R hR

end JointThermoComplexity.Complexity.FiniteRowReadSquare

#print axioms JointThermoComplexity.Complexity.FiniteRowReadSquare.coefficient_bound
#print axioms JointThermoComplexity.Complexity.FiniteRowReadSquare.encoded_hoareTime
#print axioms JointThermoComplexity.Complexity.FiniteRowReadSquare.encoded_energy_hoareTime
