module
public import proofs.JointThermoComplexity.Complexity.PowerBlockRuntime

set_option autoImplicit false
@[expose] public section

/-! Exact data/frame contracts for dispatch between the two actual power-bit blocks. -/

namespace JointThermoComplexity.Complexity.PowerBitState
open _root_.Complexity
open _root_.Complexity.TM
open BinaryIncrementRun PowerPorts

variable {arity : ℕ}

def flag (m : ℕ) : Fin (m + 13) := ⟨m + 11, by omega⟩

theorem next_ne_flag (m : ℕ) : next m ≠ flag m := by
  intro h; have hv := congrArg Fin.val h; change (2 : ℕ) = m + 11 at hv; omega
theorem accumulator_ne_flag (m : ℕ) : accumulator m ≠ flag m := by
  intro h; have hv := congrArg Fin.val h; change (3 : ℕ) = m + 11 at hv; omega
theorem power_ne_flag (m : ℕ) : power m ≠ flag m := by
  intro h; have hv := congrArg Fin.val h; change (4 : ℕ) = m + 11 at hv; omega
theorem scratch_ne_flag (m : ℕ) : scratch m ≠ flag m := by
  intro h; have hv := congrArg Fin.val h; change (5 : ℕ) = m + 11 at hv; omega

def Ready (m : ℕ) (values : Fin (m + 13) → Fin arity) (R : (Fin (m + 13) → Tape) → Prop)
    (work : Fin (m + 13) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ Register 0 (work (scratch m)) ∧ IsReg (values (next m)).val (work (next m)) ∧
    IsReg (values (accumulator m)).val (work (accumulator m)) ∧ IsReg (values (power m)).val (work (power m)) ∧ R work

def After (m : ℕ) (values : Fin (m + 13) → Fin arity) (bit : Bool) (R : (Fin (m + 13) → Tape) → Prop)
    (work : Fin (m + 13) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ Register 0 (work (scratch m)) ∧
    IsReg ((values (next m)).val + (if bit then 2 else 1)) (work (next m)) ∧
    IsReg (if bit then (values (next m)).val else (values (accumulator m)).val) (work (accumulator m)) ∧
    IsReg ((values (next m)).val + bit.toNat) (work (power m)) ∧ R work

def word (m : ℕ) (values : Fin (m + 13) → Fin arity) (bit : Bool)
    (room : bit = true → (values (next m)).val + 1 < arity) : List Bool :=
  if h : bit = true then PowerTrueBlock.word m values (room h) else PowerFalseBlock.word m values

def bound (L : ℕ) : ℕ := 192 * L ^ 2 + 360 * L + 178

end JointThermoComplexity.Complexity.PowerBitState

#print axioms JointThermoComplexity.Complexity.PowerBitState.next_ne_flag
