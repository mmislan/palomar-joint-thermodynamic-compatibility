module
public import proofs.JointThermoComplexity.Complexity.SingleVariableOutput

set_option autoImplicit false
@[expose] public section

/-! Fixed unit-gate and strict-positivity templates; input coefficients are not compiled constants. -/

namespace JointThermoComplexity.Complexity.FixedGateOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax

variable {w arity : ℕ}

def oneTermCode : List Bool := [false, false, false, false, true, true, false]
def zeroTermCode : List Bool := [false, false, false, false, false]

theorem one_code (n : ℕ) : (Term.int 1 : Term n).code = oneTermCode := rfl
theorem zero_code (n : ℕ) : (Term.int 0 : Term n).code = zeroTermCode := rfl

def unitMachine (scratch source : Fin w) : TM w :=
  SingleVariableOutput.machine scratch source [false, true, false] oneTermCode

theorem unit_hoareTime (scratch source : Fin w) (hne : source ≠ scratch) (idx : Fin arity)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (unitMachine scratch source).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work scratch) ∧ IsReg idx.val (work source) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (Formula.eq (.var idx) (.int 1)).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧ IsReg idx.val (work source) ∧ R work)
      (VariableOutput.timeBound idx.val + 13) := by
  have h := SingleVariableOutput.hoareTime scratch source hne idx before input emitted [false, true, false] oneTermCode R
  apply HoareTime.mono_bound (b := [false, true, false].length + VariableOutput.timeBound idx.val + oneTermCode.length + 3)
  · simpa only [unitMachine, Formula.code, one_code] using h
  · simp only [oneTermCode, List.length_cons, List.length_nil]
    omega

def positivePrefix : List Bool := [false, true, true] ++ zeroTermCode
def positiveMachine (scratch source : Fin w) : TM w := SingleVariableOutput.machine scratch source positivePrefix []

theorem positive_hoareTime (scratch source : Fin w) (hne : source ≠ scratch) (idx : Fin arity)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (positiveMachine scratch source).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work scratch) ∧ IsReg idx.val (work source) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (Formula.lt (.int 0) (.var idx)).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧ IsReg idx.val (work source) ∧ R work)
      (VariableOutput.timeBound idx.val + 11) := by
  have h := SingleVariableOutput.hoareTime scratch source hne idx before input emitted positivePrefix [] R
  apply HoareTime.mono_bound (b := positivePrefix.length + VariableOutput.timeBound idx.val + [].length + 3)
  · simpa only [positiveMachine, Formula.code, zero_code, positivePrefix, List.append_nil, List.append_assoc] using h
  · simp only [positivePrefix, zeroTermCode, List.length_append, List.length_cons, List.length_nil]
    omega

end JointThermoComplexity.Complexity.FixedGateOutput

#print axioms JointThermoComplexity.Complexity.FixedGateOutput.unit_hoareTime
#print axioms JointThermoComplexity.Complexity.FixedGateOutput.positive_hoareTime
