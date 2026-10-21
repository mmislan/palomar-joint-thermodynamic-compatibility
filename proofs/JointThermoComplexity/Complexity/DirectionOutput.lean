module
public import proofs.JointThermoComplexity.Complexity.FixedGateOutput
public import proofs.JointThermoComplexity.Complexity.NetworkFormula

set_option autoImplicit false
@[expose] public section

/-! Emit the exact forward or reverse direction formula using a retained runtime current address. -/

namespace JointThermoComplexity.Complexity.DirectionOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax

variable {w arity : ℕ}

def Ready (scratch source : Fin w) (v : ℕ) (R : (Fin w → Tape) → Prop) (work : Fin w → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧ IsReg v (work source) ∧ R work

def leading (forward : Bool) : List Bool := FixedGateOutput.positivePrefix ++ (if forward then [] else [true, false, false])

def machine (scratch source : Fin w) (forward : Bool) : TM w :=
  SingleVariableOutput.machine scratch source (leading forward) []

theorem code_eq (forward : Bool) (idx : Fin arity) :
    (NetworkFormula.directionFormula forward idx).code = leading forward ++ (Term.var idx).code := by
  cases forward
  · change [false, true, true] ++ ((Term.int 0 : Term arity).code ++ ([true, false, false] ++ (Term.var idx).code)) =
      (([false, true, true] ++ FixedGateOutput.zeroTermCode) ++ [true, false, false]) ++ (Term.var idx).code
    rw [FixedGateOutput.zero_code]
    simp only [List.append_assoc]
  · change [false, true, true] ++ ((Term.int 0 : Term arity).code ++ (Term.var idx).code) =
      (([false, true, true] ++ FixedGateOutput.zeroTermCode) ++ []) ++ (Term.var idx).code
    rw [FixedGateOutput.zero_code]
    simp only [List.append_nil, List.append_assoc]

theorem hoareTime (scratch source : Fin w) (hne : source ≠ scratch) (forward : Bool) (idx : Fin arity)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine scratch source forward).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready scratch source idx.val R work)
      (fun inp work out => Cursor before input (emitted ++ (NetworkFormula.directionFormula forward idx).code) inp work out ∧
        Ready scratch source idx.val R work) (VariableOutput.timeBound idx.val + 14) := by
  have hs := SingleVariableOutput.hoareTime scratch source hne idx before input emitted (leading forward) [] R
  apply HoareTime.mono_bound (b := (leading forward).length + VariableOutput.timeBound idx.val + [].length + 3)
  · simpa only [machine, Ready, code_eq, List.append_nil] using hs
  · cases forward <;> simp only [leading, FixedGateOutput.positivePrefix, FixedGateOutput.zeroTermCode,
      Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_cons, List.length_nil] <;> omega

end JointThermoComplexity.Complexity.DirectionOutput

#print axioms JointThermoComplexity.Complexity.DirectionOutput.hoareTime
