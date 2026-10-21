module
public import proofs.JointThermoComplexity.Complexity.FiniteEquationSemantics
public import proofs.JointThermoComplexity.Complexity.EquationSystemCodec

set_option autoImplicit false
@[expose] public section

/-! The actual polynomial-time machine emits exactly the faithful finite equation-system code. -/

namespace JointThermoComplexity.Complexity.FiniteEquationEncoding
open SparseInteger RealSyntax

def data (input : List Bool) : EquationSystemCodec.Data :=
  ⟨EquationVariableCount.count input, FiniteEquationSemantics.normalized input⟩

def code (input : List Bool) : List Bool := EquationSystemCodec.code (data input)

theorem binder_unary (n : ℕ) : binderCode n = SparseListCodec.unaryCode n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [HeaderControl.code_succ, SparseListCodec.unaryCode, ih]

theorem code_eq (input : List Bool) : code input = CompleteEquationFP.code input := by
  change SparseListCodec.unaryCode (EquationVariableCount.count input) ++
    (EquationSystemCodec.rowsCodec (EquationVariableCount.count input)).code
      (FiniteEquationSemantics.normalized input) = _
  rw [EquationVariableCount.normalized_code, binder_unary,
    ← FiniteEquationSemantics.normalized_natural_rows, PreorderRowCode.numericRows_finite]
  rfl

theorem code_mem_FP : code ∈ _root_.Complexity.FP := by
  have h : code = CompleteEquationFP.code := funext code_eq
  rw [h]
  exact CompleteEquationFP.code_mem_FP

theorem decode (input : List Bool) : EquationSystemCodec.decode (code input) = some (data input) :=
  EquationSystemCodec.decode_code _

theorem actual_decode (input : List Bool) :
    EquationSystemCodec.decode (CompleteEquationFP.code input) = some (data input) := by
  rw [← code_eq]
  exact decode input

theorem feasible_iff (input : List Bool) : input ∈ ETR ↔ FiniteEquationSemantics.Feasible (data input).rows :=
  FiniteEquationSemantics.normalized_satisfiable_iff input

theorem arity_pos (input : List Bool) : 0 < (data input).arity := EquationVariableCount.count_pos input

theorem arity_bound (input : List Bool) : (data input).arity ≤ 55 * (input.length + 4) :=
  EquationVariableCount.count_bound input

theorem equation_degree (input : List Bool) (p : Poly (Fin (data input).arity))
    (hp : p ∈ (data input).rows) : (interpret p).totalDegree ≤ 2 :=
  FiniteEquationSemantics.normalized_degree input p hp

theorem raw_bound (input : List Bool) (p : Poly (Fin (data input).arity))
    (hp : p ∈ (data input).rows) : SparseCircuit.RawBound 5 p :=
  FiniteEquationSemantics.normalized_raw_bound input p hp

end JointThermoComplexity.Complexity.FiniteEquationEncoding

#print axioms JointThermoComplexity.Complexity.FiniteEquationEncoding.code_eq
#print axioms JointThermoComplexity.Complexity.FiniteEquationEncoding.code_mem_FP
#print axioms JointThermoComplexity.Complexity.FiniteEquationEncoding.actual_decode
#print axioms JointThermoComplexity.Complexity.FiniteEquationEncoding.feasible_iff
