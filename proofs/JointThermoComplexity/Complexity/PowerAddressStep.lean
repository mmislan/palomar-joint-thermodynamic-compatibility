module
public import proofs.JointThermoComplexity.Complexity.PowerAddressFrame
public import proofs.JointThermoComplexity.Complexity.PowerBitStep

set_option autoImplicit false
@[expose] public section

/-! The actual input-bit step realizes natural address evolution under the remaining gate budget. -/

namespace JointThermoComplexity.Complexity.PowerAddressStep
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts PowerAddressState

theorem hoareTime (m arity L : ℕ) (ha : arity ≤ 4 * L) (s : State) (bit : Bool) (rest : List Bool)
    (hf : Fits arity (bit :: rest) s) (before tail emitted : List Bool)
    (R : (Fin (m + 13) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next m → j ≠ accumulator m → j ≠ power m → j ≠ PowerBitState.flag m → work' j = work j) → R work → R work') :
    (PowerBitStep.machine m).HoareTime
      (fun inp work out => Cursor before (bit :: tail) emitted inp work out ∧ PowerAddressFrame.Ready m s R work)
      (fun inp work out => Cursor (before ++ [bit]) tail (emitted ++ PowerAddressCode.word s bit) inp work out ∧
        PowerAddressFrame.Ready m (s.advance bit) R work) (PowerBitStep.timeBound L) := by
  obtain ⟨hn, hroom, _⟩ := step_fresh arity bit rest s hf
  let v := PowerAddressFrame.values m arity s hn hf.1 hf.2.1
  have hr : bit = true → (v (next m)).val + 1 < arity := by
    simpa only [v, PowerAddressFrame.values_next] using hroom
  have h := PowerBitStep.hoareTime m v bit hr L ha before tail emitted R hR
  exact h.consequence
    (fun _ work _ ⟨hc, hp⟩ => ⟨hc, (PowerAddressFrame.ready_iff m arity s hn hf.1 hf.2.1 R work).mpr hp⟩)
    (fun _ work _ ⟨hc, hp⟩ => ⟨by simpa only [v, PowerAddressFrame.word_eq] using hc,
      (PowerAddressFrame.after_iff m arity s hn hf.1 hf.2.1 bit R work).mp hp⟩) le_rfl

end JointThermoComplexity.Complexity.PowerAddressStep

#print axioms JointThermoComplexity.Complexity.PowerAddressStep.hoareTime
