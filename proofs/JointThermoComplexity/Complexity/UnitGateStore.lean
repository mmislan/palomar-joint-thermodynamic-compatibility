module
public import proofs.JointThermoComplexity.Complexity.StoreNext
public import proofs.JointThermoComplexity.Complexity.FixedGateOutput

set_option autoImplicit false
@[expose] public section

/-! Emit a unit equation, retain its address, and advance the next gate address. -/

namespace JointThermoComplexity.Complexity.UnitGateStore
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax

variable {w arity : ℕ}

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w) : TM (w + 1) :=
  seqTM (FixedGateOutput.unitMachine (GateStore.scratch e zero) (GateStore.next e source))
    (StoreNext.machine e source zero)

def timeBound (old value : ℕ) : ℕ := VariableOutput.timeBound value + 2 * old + 7 * value + 36

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w)
    (hne : GateStore.next e source ≠ GateStore.scratch e zero) (idx : Fin arity) (old : ℕ)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ GateStore.next e source → j ≠ CountSumAt.destination e →
      work' j = work j) → R work → R work') :
    (machine e source zero).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work (GateStore.scratch e zero)) ∧ IsReg idx.val (work (GateStore.next e source)) ∧
        IsReg old (work (CountSumAt.destination e)) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (Formula.eq (.var idx) (.int 1)).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work (GateStore.scratch e zero)) ∧
        IsReg (idx.val + 1) (work (GateStore.next e source)) ∧
        IsReg idx.val (work (CountSumAt.destination e)) ∧ R work) (timeBound old idx.val) := by
  have hemit := FixedGateOutput.unit_hoareTime (GateStore.scratch e zero) (GateStore.next e source) hne idx
    before input emitted (fun work => IsReg old (work (CountSumAt.destination e)) ∧ R work)
  have hstore := StoreNext.hoareTime e source zero hne old idx.val before input
    (emitted ++ (Formula.eq (.var idx) (.int 1)).code) R hR
  have hseq := seqTM_hoareTime
    (FixedGateOutput.unitMachine (GateStore.scratch e zero) (GateStore.next e source))
    (StoreNext.machine e source zero) hemit (by
      rintro inp work out hp
      obtain ⟨hi, hw, ho⟩ := hp.1.phase
      rw [hi, hw, ho]
      exact hp) hstore
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.UnitGateStore

#print axioms JointThermoComplexity.Complexity.UnitGateStore.hoareTime
