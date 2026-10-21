module
public import proofs.JointThermoComplexity.Complexity.NatConstantOutput
public import proofs.JointThermoComplexity.Complexity.TemplateRuntime

set_option autoImplicit false
@[expose] public section

/-! Emit denominator-times-current equals reaction-output by copying the actual binary denominator field. -/

namespace JointThermoComplexity.Complexity.CurrentEquationOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax OutputProgram

variable {w arity : ℕ}

def leading : List Bool := [false, true, false] ++ [false, true, true] ++ NatConstantOutput.intPrefix

def program (current result : Fin w) : List (Instruction w) := [.var current, .var result]

def equation (denominator : ℕ) (current result : Fin arity) : Formula arity :=
  .eq (.mul (.int (denominator : ℤ)) (.var current)) (.var result)

theorem code_eq (denominator : ℕ) (current result : Fin arity) :
    (equation denominator current result).code =
      (leading ++ BitCodec.naturalCode denominator) ++ ((Term.var current).code ++ (Term.var result).code) := by
  change [false, true, false] ++ ([false, true, true] ++ (Term.int (denominator : ℤ) : Term arity).code ++
    (Term.var current).code) ++ (Term.var result).code = _
  rw [NatConstantOutput.term_code]
  simp only [leading, List.append_assoc]

def machine (scratch current result : Fin w) : TM w := seqTM (emitBitsTM leading)
  (seqTM (PayloadFrame.machine w) (OutputProgram.machine scratch (program current result)))

theorem hoareTime (scratch current result : Fin w) (hc : current ≠ scratch) (hr : result ≠ scratch)
    (values : Fin w → Fin arity) (denominator : ℕ) (before tail emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine scratch current result).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode denominator ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧ IsReg (values current).val (work current) ∧
        IsReg (values result).val (work result) ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode denominator) tail
        (emitted ++ (equation denominator (values current) (values result)).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧ IsReg (values current).val (work current) ∧
        IsReg (values result).val (work result) ∧ R work)
      (VariableOutput.timeBound (values current).val + VariableOutput.timeBound (values result).val +
        (BitCodec.naturalCode denominator).length + 16) := by
  let P : (Fin w → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧
    IsReg (values current).val (work current) ∧ IsReg (values result).val (work result) ∧ R work
  have hprefix := FixedOutput.hoareTime leading before (BitCodec.naturalCode denominator ++ tail) emitted
    (fun work => Register 0 (work scratch) ∧ IsReg (values current).val (work current) ∧ IsReg (values result).val (work result) ∧ R work)
  have hcopy := PayloadCopy.hoareTime w denominator.bits before tail (emitted ++ leading) P
  have hvalid : Valid (program current result) scratch := by
    intro instruction hi
    simp [program] at hi
    rcases hi with rfl | rfl
    · exact hc
    · exact hr
  have hp := OutputProgram.hoareTime scratch (program current result) (fun j => (values j).val) hvalid
    (before ++ BitCodec.naturalCode denominator) tail
    ((emitted ++ leading) ++ BitCodec.naturalCode denominator) R
  have hrest := seqTM_hoareTime (PayloadFrame.machine w) (OutputProgram.machine scratch (program current result)) hcopy (by
    rintro inp work out ⟨hcur, hs, hz, hcurrent, hresult, hR⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    refine ⟨hcur, hs, hz, ?_, hR⟩
    intro instruction hin
    simp [program] at hin
    rcases hin with rfl | rfl
    · exact hcurrent
    · exact hresult) hp
  have hfull := seqTM_hoareTime (emitBitsTM leading)
    (seqTM (PayloadFrame.machine w) (OutputProgram.machine scratch (program current result))) hprefix (by
      intro inp work out hp
      obtain ⟨hi, hw, ho⟩ := hp.1.phase
      rw [hi, hw, ho]
      exact hp) hrest
  exact hfull.consequence (fun _ _ _ hp => hp) (by
    rintro inp work out ⟨hcur, hs, hz, hready, hR⟩
    refine ⟨?_, hs, hz, hready (.var current) (by simp [program]), hready (.var result) (by simp [program]), hR⟩
    rw [code_eq]
    simpa only [OutputProgram.code, program, Instruction.code, Term.code, List.append_nil,
      BitCodec.naturalCode, List.append_assoc] using hcur) (by
    simp only [leading, NatConstantOutput.intPrefix, List.length_append, List.length_cons, List.length_nil,
      OutputProgram.timeBound, program, Instruction.timeBound, BitCodec.naturalCode]
    omega)

theorem decoded_bound (current result denominator L : ℕ) (hc : current ≤ 4 * L) (hr : result ≤ 4 * L)
    (hd : (BitCodec.naturalCode denominator).length ≤ L) :
    VariableOutput.timeBound current + VariableOutput.timeBound result + (BitCodec.naturalCode denominator).length + 16 ≤
      64 * L ^ 2 + 97 * L + 52 := by
  have ha := TemplateRuntime.variable_bound hc
  have hb := TemplateRuntime.variable_bound hr
  omega

end JointThermoComplexity.Complexity.CurrentEquationOutput

#print axioms JointThermoComplexity.Complexity.CurrentEquationOutput.hoareTime
#print axioms JointThermoComplexity.Complexity.CurrentEquationOutput.decoded_bound
