module
public import proofs.JointThermoComplexity.Complexity.PowerGateStore

set_option autoImplicit false
@[expose] public section

/-! The actual false-payload-bit block squares the power and advances one gate address. -/

namespace JointThermoComplexity.Complexity.PowerFalseBlock
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun PowerPorts

variable {arity : ℕ}

def machine (m : ℕ) : TM (m + 13) :=
  GateStore.machine (powerPermutation m) (nextOld m) (scratchOld m) (power m) (power m)

def word (m : ℕ) (values : Fin (m + 13) → Fin arity) : List Bool :=
  BinaryPowerCode.multiply (values (next m)) (values (power m)) (values (power m))

def timeBound (m : ℕ) (values : Fin (m + 13) → Fin arity) : ℕ :=
  GateStore.timeBound (fun j => (values j).val) (values (power m)).val (next m) (power m) (power m)

theorem hoareTime (m : ℕ) (values : Fin (m + 13) → Fin arity) (before input emitted : List Bool)
    (R : (Fin (m + 13) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next m → j ≠ accumulator m → j ≠ power m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register 0 (work (scratch m)) ∧
        IsReg (values (next m)).val (work (next m)) ∧ IsReg (values (accumulator m)).val (work (accumulator m)) ∧
        IsReg (values (power m)).val (work (power m)) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ word m values) inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work (scratch m)) ∧ IsReg ((values (next m)).val + 1) (work (next m)) ∧
        IsReg (values (accumulator m)).val (work (accumulator m)) ∧ IsReg (values (next m)).val (work (power m)) ∧ R work)
      (timeBound m values) := by
  let P : (Fin (m + 13) → Tape) → Prop := fun work => IsReg (values (accumulator m)).val (work (accumulator m)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ next m → j ≠ power m → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨ha, hr⟩
    exact ⟨by simpa only [hw _ (next_ne_accumulator m).symm (accumulator_ne_power m)] using ha,
      hR work work' (fun j hn _ hp => hw j hn hp) hr⟩
  have h := PowerGateStore.hoareTime m (powerPermutation m) (nextOld m) (scratchOld m) (power m) (power m) (power m)
    (power_next m) (power_scratch m) (power_destination m) (power_ne_scratch m) (power_ne_scratch m)
    values (values (power m)).val before input emitted P hP
  exact h.consequence
    (fun _ _ _ ⟨hc, hs, hz, hn, ha, hp, hr⟩ => ⟨hc, hs, hz, hn, hp, hp, hp, ha, hr⟩)
    (fun _ _ _ ⟨hc, hs, hz, hn, hp, ha, hr⟩ => ⟨by simpa only [word, GateStoreCircuit.code_eq] using hc, hs, hz, hn, ha, hp, hr⟩) le_rfl

end JointThermoComplexity.Complexity.PowerFalseBlock

#print axioms JointThermoComplexity.Complexity.PowerFalseBlock.hoareTime
