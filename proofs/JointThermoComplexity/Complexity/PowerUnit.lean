module
public import proofs.JointThermoComplexity.Complexity.UnitGateStore
public import proofs.JointThermoComplexity.Complexity.PowerAddressFrame
public import proofs.JointThermoComplexity.Complexity.TemplateRuntime

set_option autoImplicit false
@[expose] public section

/-! Initialize the repeated-squaring accumulator with an actual unit gate. -/

namespace JointThermoComplexity.Complexity.PowerUnit
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts PowerAddressState

def unitState (s : State) : State := ⟨s.nextAddress + 1, s.nextAddress, s.powerAddress⟩

def machine (m : ℕ) : TM (m + 13) :=
  UnitGateStore.machine (accumulatorPermutation m) (nextOld m) (scratchOld m)

theorem hoareTime (m arity : ℕ) (s : State) (hn : s.nextAddress < arity)
    (before input emitted : List Bool) (R : (Fin (m + 13) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next m → j ≠ accumulator m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ PowerAddressFrame.Ready m s R work)
      (fun inp work out => Cursor before input
        (emitted ++ (RealSyntax.Formula.eq (.var (⟨s.nextAddress, hn⟩ : Fin arity)) (.int 1)).code) inp work out ∧
        PowerAddressFrame.Ready m (unitState s) R work)
      (UnitGateStore.timeBound s.accumulatorAddress s.nextAddress) := by
  have hne : GateStore.next (accumulatorPermutation m) (nextOld m) ≠
      GateStore.scratch (accumulatorPermutation m) (scratchOld m) := by
    simpa only [accumulator_next, accumulator_scratch] using next_ne_scratch m
  let P : (Fin (m + 13) → Tape) → Prop := fun work => IsReg s.powerAddress (work (power m)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ GateStore.next (accumulatorPermutation m) (nextOld m) →
      j ≠ CountSumAt.destination (accumulatorPermutation m) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hp, hr⟩
    have hw' : ∀ j, j ≠ next m → j ≠ accumulator m → work' j = work j := by
      simpa only [accumulator_next, accumulator_destination] using hw
    exact ⟨by simpa only [hw' _ (next_ne_power m).symm (accumulator_ne_power m).symm] using hp,
      hR work work' hw' hr⟩
  have h := UnitGateStore.hoareTime (accumulatorPermutation m) (nextOld m) (scratchOld m) hne
    (⟨s.nextAddress, hn⟩ : Fin arity) s.accumulatorAddress before input emitted P hP
  simpa only [machine, PowerAddressFrame.Ready, unitState, P, accumulator_next, accumulator_scratch,
    accumulator_destination] using h

theorem runtime_bound (s : State) (L : ℕ) (hn : s.nextAddress ≤ 4 * L) (ha : s.accumulatorAddress ≤ 4 * L) :
    UnitGateStore.timeBound s.accumulatorAddress s.nextAddress ≤ 32 * L ^ 2 + 84 * L + 54 := by
  have hv := TemplateRuntime.variable_bound hn
  unfold UnitGateStore.timeBound
  omega

end JointThermoComplexity.Complexity.PowerUnit

#print axioms JointThermoComplexity.Complexity.PowerUnit.hoareTime
