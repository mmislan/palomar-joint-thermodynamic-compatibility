module
public import proofs.JointThermoComplexity.Complexity.NatConstantOutput
public import proofs.JointThermoComplexity.Complexity.StoreNext
public import proofs.JointThermoComplexity.Complexity.TemplateRuntime

set_option autoImplicit false
@[expose] public section

/-! A runtime binary constant gate stores its fresh output reference and advances the gate address. -/

namespace JointThermoComplexity.Complexity.NatConstantStore
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax

variable {w arity : ℕ}

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w) : TM (w + 1) :=
  seqTM (NatConstantOutput.machine (GateStore.scratch e zero) (GateStore.next e source)) (StoreNext.machine e source zero)

def timeBound (old target value : ℕ) : ℕ :=
  VariableOutput.timeBound target + (BitCodec.naturalCode value).length + 2 * old + 7 * target + 36

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w)
    (hne : GateStore.next e source ≠ GateStore.scratch e zero) (idx : Fin arity) (old value : ℕ)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ GateStore.next e source → j ≠ CountSumAt.destination e →
      work' j = work j) → R work → R work') :
    (machine e source zero).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work (GateStore.scratch e zero)) ∧
        IsReg idx.val (work (GateStore.next e source)) ∧ IsReg old (work (CountSumAt.destination e)) ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail
        (emitted ++ (Formula.eq (.var idx) (.int (value : ℤ))).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work (GateStore.scratch e zero)) ∧
        IsReg (idx.val + 1) (work (GateStore.next e source)) ∧
        IsReg idx.val (work (CountSumAt.destination e)) ∧ R work) (timeBound old idx.val value) := by
  have hemit := NatConstantOutput.hoareTime (GateStore.scratch e zero) (GateStore.next e source) hne idx value
    before tail emitted (fun work => IsReg old (work (CountSumAt.destination e)) ∧ R work)
  have hstore := StoreNext.hoareTime e source zero hne old idx.val (before ++ BitCodec.naturalCode value) tail
    (emitted ++ (Formula.eq (.var idx) (.int (value : ℤ))).code) R hR
  have hseq := seqTM_hoareTime
    (NatConstantOutput.machine (GateStore.scratch e zero) (GateStore.next e source)) (StoreNext.machine e source zero) hemit (by
      rintro inp work out hp
      obtain ⟨hi, hw, ho⟩ := hp.1.phase
      rw [hi, hw, ho]
      exact hp) hstore
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold timeBound; omega)

theorem runtime_bound (old target value L : ℕ) (ho : old ≤ 4 * L) (ht : target ≤ 4 * L)
    (hv : (BitCodec.naturalCode value).length ≤ L) :
    timeBound old target value ≤ 32 * L ^ 2 + 85 * L + 54 := by
  have h := TemplateRuntime.variable_bound ht
  unfold timeBound
  omega

end JointThermoComplexity.Complexity.NatConstantStore

#print axioms JointThermoComplexity.Complexity.NatConstantStore.hoareTime
