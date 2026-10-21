module
public import proofs.JointThermoComplexity.Complexity.StoreNext
public import proofs.JointThermoComplexity.Complexity.BinaryGateOutput
public import proofs.JointThermoComplexity.Complexity.GateStoreRuntime

set_option autoImplicit false
@[expose] public section

/-! Actual addition equation emission followed by result-address storage and next-address increment. -/

namespace JointThermoComplexity.Complexity.AddGateStore
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun

variable {w arity : ℕ}

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w) (left right : Fin (w + 1)) : TM (w + 1) :=
  seqTM (BinaryGateOutput.machine false (GateStore.scratch e zero) (GateStore.next e source) left right)
    (StoreNext.machine e source zero)

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w) (left right : Fin (w + 1))
    (ht : GateStore.next e source ≠ GateStore.scratch e zero)
    (hl : left ≠ GateStore.scratch e zero) (hr : right ≠ GateStore.scratch e zero)
    (values : Fin (w + 1) → Fin arity) (old : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ GateStore.next e source → j ≠ CountSumAt.destination e →
      work' j = work j) → R work → R work') :
    (machine e source zero left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work (GateStore.scratch e zero)) ∧ IsReg (values (GateStore.next e source)).val (work (GateStore.next e source)) ∧
        IsReg (values left).val (work left) ∧ IsReg (values right).val (work right) ∧
        IsReg old (work (CountSumAt.destination e)) ∧ R work)
      (fun inp work out => Cursor before input
        (emitted ++ (BinaryGateOutput.formula false values (GateStore.next e source) left right).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work (GateStore.scratch e zero)) ∧
        IsReg ((values (GateStore.next e source)).val + 1) (work (GateStore.next e source)) ∧
        IsReg (values (GateStore.next e source)).val (work (CountSumAt.destination e)) ∧ R work)
      (GateStore.timeBound (fun j => (values j).val) old (GateStore.next e source) left right) := by
  have hemit := BinaryGateOutput.hoareTime false (GateStore.scratch e zero) (GateStore.next e source) left right ht hl hr
    values before input emitted (fun work => IsReg old (work (CountSumAt.destination e)) ∧ R work)
  have hstore := StoreNext.hoareTime e source zero ht old (values (GateStore.next e source)).val before input
    (emitted ++ (BinaryGateOutput.formula false values (GateStore.next e source) left right).code) R hR
  have hseq := seqTM_hoareTime
    (BinaryGateOutput.machine false (GateStore.scratch e zero) (GateStore.next e source) left right)
    (StoreNext.machine e source zero) hemit (by
      rintro inp work out ⟨hc, hs, hz, hn, _, _, hd, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, hz, hn, hd, hr⟩) hstore
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
    (by unfold GateStore.timeBound; dsimp only; omega)

end JointThermoComplexity.Complexity.AddGateStore

#print axioms JointThermoComplexity.Complexity.AddGateStore.hoareTime
