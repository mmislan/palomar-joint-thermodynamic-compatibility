module
public import proofs.JointThermoComplexity.Complexity.StoreNext
public import proofs.JointThermoComplexity.Complexity.UnaryGateOutput

set_option autoImplicit false
@[expose] public section

/-! Emit a copy/negation equation before overwriting its chosen result register. -/

namespace JointThermoComplexity.Complexity.UnaryGateStore
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun

variable {w arity : ℕ}

def machine (negate : Bool) (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w)
    (operand : Fin (w + 1)) : TM (w + 1) :=
  seqTM (UnaryGateOutput.machine negate (GateStore.scratch e zero) (GateStore.next e source) operand)
    (StoreNext.machine e source zero)

def timeBound (values : Fin (w + 1) → ℕ) (old : ℕ) (target operand : Fin (w + 1)) : ℕ :=
  UnaryGateOutput.timeBound values target operand + 2 * old + 7 * values target + 23

theorem hoareTime (negate : Bool) (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w)
    (operand : Fin (w + 1)) (ht : GateStore.next e source ≠ GateStore.scratch e zero)
    (hf : operand ≠ GateStore.scratch e zero) (values : Fin (w + 1) → Fin arity) (old : ℕ)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ GateStore.next e source → j ≠ CountSumAt.destination e →
      work' j = work j) → R work → R work') :
    (machine negate e source zero operand).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work (GateStore.scratch e zero)) ∧ IsReg (values (GateStore.next e source)).val (work (GateStore.next e source)) ∧
        IsReg (values operand).val (work operand) ∧ IsReg old (work (CountSumAt.destination e)) ∧ R work)
      (fun inp work out => Cursor before input
        (emitted ++ (UnaryGateOutput.formula negate values (GateStore.next e source) operand).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work (GateStore.scratch e zero)) ∧
        IsReg ((values (GateStore.next e source)).val + 1) (work (GateStore.next e source)) ∧
        IsReg (values (GateStore.next e source)).val (work (CountSumAt.destination e)) ∧ R work)
      (timeBound (fun j => (values j).val) old (GateStore.next e source) operand) := by
  have hemit := UnaryGateOutput.hoareTime negate (GateStore.scratch e zero) (GateStore.next e source) operand ht hf
    values before input emitted (fun work => IsReg old (work (CountSumAt.destination e)) ∧ R work)
  have hstore := StoreNext.hoareTime e source zero ht old (values (GateStore.next e source)).val before input
    (emitted ++ (UnaryGateOutput.formula negate values (GateStore.next e source) operand).code) R hR
  have hseq := seqTM_hoareTime
    (UnaryGateOutput.machine negate (GateStore.scratch e zero) (GateStore.next e source) operand)
    (StoreNext.machine e source zero) hemit (by
      rintro inp work out ⟨hc, hs, hz, hn, _, hd, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, hz, hn, hd, hr⟩) hstore
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold timeBound; dsimp only; omega)

end JointThermoComplexity.Complexity.UnaryGateStore

#print axioms JointThermoComplexity.Complexity.UnaryGateStore.hoareTime
