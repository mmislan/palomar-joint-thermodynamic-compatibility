module
public import proofs.JointThermoComplexity.Complexity.PowerFalseBlock
public import proofs.JointThermoComplexity.Complexity.PowerTrueValues

set_option autoImplicit false
@[expose] public section

/-! The actual true-payload-bit block emits accumulator-times-power, then the old-power square. -/

namespace JointThermoComplexity.Complexity.PowerTrueBlock
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun PowerPorts

variable {arity : ℕ}

def first (m : ℕ) : TM (m + 13) :=
  GateStore.machine (accumulatorPermutation m) (nextOld m) (scratchOld m) (accumulator m) (power m)

def machine (m : ℕ) : TM (m + 13) := seqTM (first m) (PowerFalseBlock.machine m)

def word (m : ℕ) (values : Fin (m + 13) → Fin arity) (room : (values (next m)).val + 1 < arity) : List Bool :=
  BinaryPowerCode.multiply (values (next m)) (values (accumulator m)) (values (power m)) ++
    PowerFalseBlock.word m (PowerTrueValues.afterFirst m values room)

def timeBound (m : ℕ) (values : Fin (m + 13) → Fin arity) (room : (values (next m)).val + 1 < arity) : ℕ :=
  GateStore.timeBound (fun j => (values j).val) (values (accumulator m)).val (next m) (accumulator m) (power m) + 1 +
    PowerFalseBlock.timeBound m (PowerTrueValues.afterFirst m values room)

theorem word_eq (m : ℕ) (values : Fin (m + 13) → Fin arity) (room : (values (next m)).val + 1 < arity) :
    word m values room =
      BinaryPowerCode.multiply (values (next m)) (values (accumulator m)) (values (power m)) ++
        BinaryPowerCode.multiply ⟨(values (next m)).val + 1, room⟩ (values (power m)) (values (power m)) := by
  simp only [word, PowerFalseBlock.word, PowerTrueValues.next_value, PowerTrueValues.power_value]

theorem hoareTime (m : ℕ) (values : Fin (m + 13) → Fin arity) (room : (values (next m)).val + 1 < arity)
    (before input emitted : List Bool) (R : (Fin (m + 13) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next m → j ≠ accumulator m → j ≠ power m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register 0 (work (scratch m)) ∧
        IsReg (values (next m)).val (work (next m)) ∧ IsReg (values (accumulator m)).val (work (accumulator m)) ∧
        IsReg (values (power m)).val (work (power m)) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ word m values room) inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work (scratch m)) ∧ IsReg ((values (next m)).val + 2) (work (next m)) ∧
        IsReg (values (next m)).val (work (accumulator m)) ∧ IsReg ((values (next m)).val + 1) (work (power m)) ∧ R work)
      (timeBound m values room) := by
  rintro inp work out ⟨hc, hs, hz, hn, ha, hp, hr⟩
  let P : (Fin (m + 13) → Tape) → Prop := fun work => IsReg (values (power m)).val (work (power m)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ next m → j ≠ accumulator m → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hp, hr⟩
    exact ⟨by simpa only [hw _ (next_ne_power m).symm (accumulator_ne_power m).symm] using hp,
      hR work work' (fun j hn ha _ => hw j hn ha) hr⟩
  obtain ⟨c, tc, htc, hcreach, hchalt, hccur, hcsafe, hczero, hcnext, hcacc, hcpower, hcR⟩ :=
    PowerGateStore.hoareTime m (accumulatorPermutation m) (nextOld m) (scratchOld m)
      (accumulator m) (accumulator m) (power m) (accumulator_next m) (accumulator_scratch m) (accumulator_destination m)
      (accumulator_ne_scratch m) (power_ne_scratch m) values (values (accumulator m)).val before input emitted P hP
      inp work out ⟨hc, hs, hz, hn, ha, hp, ha, hp, hr⟩
  let values' := PowerTrueValues.afterFirst m values room
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdsafe, hdzero, hdnext, hdacc, hdpower, hdR⟩ :=
    PowerFalseBlock.hoareTime m values' before input
      (emitted ++ (BinaryGateOutput.formula true values (next m) (accumulator m) (power m)).code) R hR
      c.input c.work c.output ⟨hccur, hcsafe, hczero,
        by simpa only [values', PowerTrueValues.next_value] using hcnext,
        by simpa only [values', PowerTrueValues.accumulator_value] using hcacc,
        by simpa only [values', PowerTrueValues.power_value] using hcpower, hcR⟩
  obtain ⟨hi, hw, ho⟩ := hccur.phase
  have hrr : (PowerFalseBlock.machine m).reachesIn td
      ⟨(PowerFalseBlock.machine m).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, ho] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (first m) (PowerFalseBlock.machine m) hcreach hchalt hrr
  have hbound : tc + 1 + td ≤
      GateStore.timeBound (fun j => (values j).val) (values (accumulator m)).val (next m) (accumulator m) (power m) + 1 +
        PowerFalseBlock.timeBound m values' := Nat.add_le_add (Nat.add_le_add_right htc 1) htd
  exact ⟨phase2Wrap (first m) (PowerFalseBlock.machine m) d, tc + 1 + td, hbound,
    hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt,
    by simpa only [phase2Wrap, word, values', GateStoreCircuit.code_eq, List.append_assoc] using hdcur, hdsafe, hdzero,
    by simpa only [phase2Wrap, values', PowerTrueValues.next_value, Nat.add_assoc] using hdnext,
    by simpa only [phase2Wrap, values', PowerTrueValues.accumulator_value] using hdacc,
    by simpa only [phase2Wrap, values', PowerTrueValues.next_value] using hdpower, hdR⟩

end JointThermoComplexity.Complexity.PowerTrueBlock

#print axioms JointThermoComplexity.Complexity.PowerTrueBlock.hoareTime
