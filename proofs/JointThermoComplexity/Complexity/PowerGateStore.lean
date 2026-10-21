module
public import proofs.JointThermoComplexity.Complexity.PowerPorts
public import proofs.JointThermoComplexity.Complexity.GateStoreCircuit

set_option autoImplicit false
@[expose] public section

/-! Normalize the actual gate-store contract at the fixed repeated-squaring ports. -/

namespace JointThermoComplexity.Complexity.PowerGateStore
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun PowerPorts

variable {arity : ℕ}

theorem hoareTime (m : ℕ) (e : Fin (m + 13) ≃ Fin (m + 13)) (source zero : Fin (m + 12))
    (result left right : Fin (m + 13))
    (heN : GateStore.next e source = next m) (heS : GateStore.scratch e zero = scratch m) (heD : CountSumAt.destination e = result)
    (hl : left ≠ scratch m) (hr : right ≠ scratch m) (values : Fin (m + 13) → Fin arity) (old : ℕ)
    (before input emitted : List Bool) (R : (Fin (m + 13) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next m → j ≠ result → work' j = work j) → R work → R work') :
    (GateStore.machine e source zero left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work (scratch m)) ∧ IsReg (values (next m)).val (work (next m)) ∧
        IsReg (values left).val (work left) ∧ IsReg (values right).val (work right) ∧ IsReg old (work result) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (BinaryGateOutput.formula true values (next m) left right).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work (scratch m)) ∧ IsReg ((values (next m)).val + 1) (work (next m)) ∧
        IsReg (values (next m)).val (work result) ∧ R work)
      (GateStore.timeBound (fun j => (values j).val) old (next m) left right) := by
  have hn : GateStore.next e source ≠ GateStore.scratch e zero := by
    simpa only [heN, heS] using next_ne_scratch m
  have hl' : left ≠ GateStore.scratch e zero := by simpa only [heS] using hl
  have hr' : right ≠ GateStore.scratch e zero := by simpa only [heS] using hr
  have hR' : ∀ work work', (∀ j, j ≠ GateStore.next e source → j ≠ CountSumAt.destination e → work' j = work j) → R work → R work' := by
    intro work work' hw h
    exact hR work work' (by simpa only [heN, heD] using hw) h
  simpa only [heN, heS, heD] using GateStore.hoareTime e source zero left right hn hl' hr' values old before input emitted R hR'

end JointThermoComplexity.Complexity.PowerGateStore

#print axioms JointThermoComplexity.Complexity.PowerGateStore.hoareTime
