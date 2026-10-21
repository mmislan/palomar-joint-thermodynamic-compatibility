module
public import proofs.JointThermoComplexity.Complexity.PowerAddressCode
public import proofs.JointThermoComplexity.Complexity.PowerBitState

set_option autoImplicit false
@[expose] public section

/-! Relate natural register states to the typed per-bit machine contract without restricting the final cursor. -/

namespace JointThermoComplexity.Complexity.PowerAddressFrame
open _root_.Complexity
open _root_.Complexity.TM
open PowerPorts PowerAddressState BinaryIncrementRun

def Ready (m : ℕ) (s : State) (R : (Fin (m + 13) → Tape) → Prop) (work : Fin (m + 13) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ Register 0 (work (scratch m)) ∧ IsReg s.nextAddress (work (next m)) ∧
    IsReg s.accumulatorAddress (work (accumulator m)) ∧ IsReg s.powerAddress (work (power m)) ∧ R work

def values (m arity : ℕ) (s : State) (hn : s.nextAddress < arity) (ha : s.accumulatorAddress < arity)
    (hp : s.powerAddress < arity) : Fin (m + 13) → Fin arity := fun j =>
  if j = next m then ⟨s.nextAddress, hn⟩ else if j = accumulator m then ⟨s.accumulatorAddress, ha⟩ else ⟨s.powerAddress, hp⟩

theorem values_next (m arity : ℕ) (s : State) (hn : s.nextAddress < arity) (ha : s.accumulatorAddress < arity) (hp : s.powerAddress < arity) :
    values m arity s hn ha hp (next m) = ⟨s.nextAddress, hn⟩ := by simp only [values, ↓reduceIte]

theorem values_accumulator (m arity : ℕ) (s : State) (hn : s.nextAddress < arity) (ha : s.accumulatorAddress < arity) (hp : s.powerAddress < arity) :
    values m arity s hn ha hp (accumulator m) = ⟨s.accumulatorAddress, ha⟩ := by
  simp only [values, (next_ne_accumulator m).symm, ↓reduceIte]

theorem values_power (m arity : ℕ) (s : State) (hn : s.nextAddress < arity) (ha : s.accumulatorAddress < arity) (hp : s.powerAddress < arity) :
    values m arity s hn ha hp (power m) = ⟨s.powerAddress, hp⟩ := by
  simp only [values, (next_ne_power m).symm, (accumulator_ne_power m).symm, ↓reduceIte]

theorem ready_iff (m arity : ℕ) (s : State) (hn : s.nextAddress < arity) (ha : s.accumulatorAddress < arity) (hp : s.powerAddress < arity)
    (R : (Fin (m + 13) → Tape) → Prop) (work : Fin (m + 13) → Tape) :
    PowerBitState.Ready m (values m arity s hn ha hp) R work ↔ Ready m s R work := by
  simp only [PowerBitState.Ready, Ready, values_next, values_accumulator, values_power]

theorem after_iff (m arity : ℕ) (s : State) (hn : s.nextAddress < arity) (ha : s.accumulatorAddress < arity) (hp : s.powerAddress < arity)
    (bit : Bool) (R : (Fin (m + 13) → Tape) → Prop) (work : Fin (m + 13) → Tape) :
    PowerBitState.After m (values m arity s hn ha hp) bit R work ↔ Ready m (s.advance bit) R work := by
  cases bit <;> simp only [PowerBitState.After, Ready, State.advance, values_next, values_accumulator,
    Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]

theorem word_eq (m arity : ℕ) (s : State) (hn : s.nextAddress < arity) (ha : s.accumulatorAddress < arity) (hp : s.powerAddress < arity)
    (bit : Bool) (room : bit = true → (values m arity s hn ha hp (next m)).val + 1 < arity) :
    PowerBitState.word m (values m arity s hn ha hp) bit room = PowerAddressCode.word s bit := by
  cases bit <;> simp only [PowerBitState.word, Bool.false_eq_true, ↓reduceDIte, PowerFalseBlock.word,
    PowerTrueBlock.word_eq, PowerAddressCode.typed_multiply, values_next, values_accumulator, values_power, PowerAddressCode.word]

end JointThermoComplexity.Complexity.PowerAddressFrame

#print axioms JointThermoComplexity.Complexity.PowerAddressFrame.word_eq
