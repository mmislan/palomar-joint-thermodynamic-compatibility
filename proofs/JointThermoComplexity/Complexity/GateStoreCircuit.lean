module
public import proofs.JointThermoComplexity.Complexity.GateStore
public import proofs.JointThermoComplexity.Complexity.BinaryPowerCode

set_option autoImplicit false
@[expose] public section

/-! Actual multiplication emission extends the corresponding forward circuit equation stream. -/

namespace JointThermoComplexity.Complexity.GateStoreCircuit
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax RealCircuit CircuitSerialization

variable {w n k arity : ℕ}

theorem code_eq (values : Fin (w + 1) → Fin arity) (target left right : Fin (w + 1)) :
    (BinaryGateOutput.formula true values target left right).code =
      BinaryPowerCode.multiply (values target) (values left) (values right) := rfl

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w) (left right : Fin (w + 1))
    (hn : GateStore.next e source ≠ GateStore.scratch e zero)
    (hl : left ≠ GateStore.scratch e zero) (hr : right ≠ GateStore.scratch e zero)
    (values : Fin (w + 1) → Fin arity) (old : ℕ)
    (circuit : Circuit n k) (lref rref : Fin k) (inputs : Fin n → Fin arity) (outputs : Fin (k + 1) → Fin arity)
    (htarget : values (GateStore.next e source) = outputs (Fin.last k))
    (hleft : values left = outputs lref.castSucc) (hright : values right = outputs rref.castSucc)
    (before input leading : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ GateStore.next e source → j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (GateStore.machine e source zero left right).HoareTime
      (fun inp work out => Cursor before input
          (leading ++ equationStream circuit inputs (fun i => outputs i.castSucc)) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work (GateStore.scratch e zero)) ∧
        IsReg (values (GateStore.next e source)).val (work (GateStore.next e source)) ∧
        IsReg (values left).val (work left) ∧ IsReg (values right).val (work right) ∧
        IsReg old (work (CountSumAt.destination e)) ∧ R work)
      (fun inp work out => Cursor before input
          (leading ++ equationStream (circuit.snoc (.mul lref rref)) inputs outputs) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work (GateStore.scratch e zero)) ∧
        IsReg ((values (GateStore.next e source)).val + 1) (work (GateStore.next e source)) ∧
        IsReg (values (GateStore.next e source)).val (work (CountSumAt.destination e)) ∧ R work)
      (GateStore.timeBound (fun j => (values j).val) old (GateStore.next e source) left right) := by
  have h := GateStore.hoareTime e source zero left right hn hl hr values old before input
    (leading ++ equationStream circuit inputs (fun i => outputs i.castSucc)) R hR
  apply h.strengthen_post
  rintro inp work out ⟨hc, hs, hz, hnext, hresult, hrest⟩
  refine ⟨?_, hs, hz, hnext, hresult, hrest⟩
  have hcode : (BinaryGateOutput.formula true values (GateStore.next e source) left right).code =
      BinaryPowerCode.multiply (outputs (Fin.last k)) (outputs lref.castSucc) (outputs rref.castSucc) := by
    rw [code_eq, htarget, hleft, hright]
  simpa only [equationStream, Step.term, hcode, BinaryPowerCode.multiply, List.append_assoc] using hc

end JointThermoComplexity.Complexity.GateStoreCircuit

#print axioms JointThermoComplexity.Complexity.GateStoreCircuit.hoareTime
