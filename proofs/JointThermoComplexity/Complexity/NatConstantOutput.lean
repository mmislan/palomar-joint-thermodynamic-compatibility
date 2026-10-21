module
public import proofs.JointThermoComplexity.Complexity.PayloadCopy
public import proofs.JointThermoComplexity.Complexity.SingleVariableOutput

set_option autoImplicit false
@[expose] public section

/-! Emit an integer constant gate by copying its actual canonical natural field in binary. -/

namespace JointThermoComplexity.Complexity.NatConstantOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax

variable {w arity : ℕ}

def eqTag : List Bool := [false, true, false]
def intPrefix : List Bool := [false, false, false, false]

theorem term_code (value : ℕ) : (Term.int (value : ℤ) : Term arity).code = intPrefix ++ BitCodec.naturalCode value := rfl

theorem code_eq (idx : Fin arity) (value : ℕ) :
    (Formula.eq (.var idx) (.int (value : ℤ))).code =
      (eqTag ++ (Term.var idx).code ++ intPrefix) ++ BitCodec.naturalCode value := by
  simp only [Formula.code, term_code, eqTag, List.append_assoc]

def machine (scratch source : Fin w) : TM w :=
  seqTM (SingleVariableOutput.machine scratch source eqTag intPrefix) (PayloadFrame.machine w)

theorem hoareTime (scratch source : Fin w) (hne : source ≠ scratch) (idx : Fin arity) (value : ℕ)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine scratch source).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧ IsReg idx.val (work source) ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail
        (emitted ++ (Formula.eq (.var idx) (.int (value : ℤ))).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧ IsReg idx.val (work source) ∧ R work)
      (VariableOutput.timeBound idx.val + (BitCodec.naturalCode value).length + 13) := by
  let P : (Fin w → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧
    Register 0 (work scratch) ∧ IsReg idx.val (work source) ∧ R work
  have hprefix := SingleVariableOutput.hoareTime scratch source hne idx before
    (BitCodec.naturalCode value ++ tail) emitted eqTag intPrefix R
  have hcopy := PayloadCopy.hoareTime w value.bits before tail
    (emitted ++ (eqTag ++ (Term.var idx).code ++ intPrefix)) P
  have hseq := seqTM_hoareTime (SingleVariableOutput.machine scratch source eqTag intPrefix)
    (PayloadFrame.machine w) hprefix (by
      rintro inp work out hp
      obtain ⟨hi, hw, ho⟩ := hp.1.phase
      rw [hi, hw, ho]
      exact hp) hcopy
  exact hseq.consequence (fun _ _ _ hp => hp) (by
    rintro inp work out ⟨hc, hs, hz, hn, hr⟩
    refine ⟨?_, hs, hz, hn, hr⟩
    rw [code_eq]
    simpa only [BitCodec.naturalCode, List.append_assoc] using hc)
    (by simp only [eqTag, intPrefix, List.length_cons, List.length_nil, BitCodec.naturalCode]; omega)

end JointThermoComplexity.Complexity.NatConstantOutput

#print axioms JointThermoComplexity.Complexity.NatConstantOutput.hoareTime
