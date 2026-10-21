module
public import proofs.JointThermoComplexity.Complexity.SparseOffsetCode
public import proofs.JointThermoComplexity.Complexity.BinaryConstantAdd

set_option autoImplicit false
@[expose] public section

/-! Total offset/row-count control for a marked sparse polynomial pass. -/

namespace JointThermoComplexity.Complexity.CountedSparseControl

structure State where
  base : SparseOffsetLoopControl.State
  rows : ℕ

def increment (s : State) : ℕ :=
  if s.base.running then
    if SourceBitRead.value s.base.input then SparseTermOffsetControl.count (BooleanMachine.suffix s.base.input) else 0
  else 0

def step (boxed : Bool) (s : State) : State := ⟨SparseOffsetLoopControl.step boxed s.base, s.rows + increment s⟩

def run (boxed : Bool) : ℕ → State → State
  | 0, s => s
  | k + 1, s => run boxed k (step boxed s)

theorem run_succ_last (boxed : Bool) (k : ℕ) (s : State) :
    run boxed (k + 1) s = step boxed (run boxed k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih (step boxed s)

theorem run_base (boxed : Bool) (k : ℕ) (s : State) :
    (run boxed k s).base = SparseOffsetLoopControl.run boxed k s.base := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih (step boxed s)

theorem increment_le (s : State) : increment s ≤ 16 := by
  unfold increment
  split
  · split
    · exact SparseTermOffsetControl.count_le _
    · omega
  · omega

theorem step_stopped (boxed : Bool) (s : State) (hs : s.base.running = false) : step boxed s = s := by
  cases s with
  | mk base rows =>
    change base.running = false at hs
    simp only [step, increment, SparseOffsetLoopControl.step, hs, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

theorem run_stopped (boxed : Bool) (k : ℕ) (s : State) (hs : s.base.running = false) : run boxed k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [run, step_stopped boxed s hs] using ih

theorem run_rows_bound (boxed : Bool) (k : ℕ) (s : State) : (run boxed k s).rows ≤ s.rows + 16 * k := by
  induction k generalizing s with
  | zero => simp only [run, Nat.mul_zero, Nat.add_zero, le_refl]
  | succ k ih =>
    have hi := ih (step boxed s)
    have hs := increment_le s
    change (run boxed k (step boxed s)).rows ≤ _
    change (run boxed k (step boxed s)).rows ≤ s.rows + increment s + 16 * k at hi
    omega

theorem run_row_bits (boxed : Bool) (k : ℕ) (s : State) :
    (run boxed k s).rows.bits.length ≤ s.rows.bits.length + 16 * k := by
  induction k generalizing s with
  | zero => simp only [run, Nat.mul_zero, Nat.add_zero, le_refl]
  | succ k ih =>
    have hi := ih (step boxed s)
    have hs := (BinaryConstantAdd.bits_add s.rows (increment s)).trans
      (Nat.add_le_add_left (increment_le s) s.rows.bits.length)
    change (run boxed k (step boxed s)).rows.bits.length ≤ _
    change (run boxed k (step boxed s)).rows.bits.length ≤ (s.rows + increment s).bits.length + 16 * k at hi
    omega

theorem run_bounds (boxed : Bool) (k : ℕ) (s : State) (L : ℕ) (hL : s.base.input.length ≤ L) :
    (run boxed k s).base.input.length ≤ s.base.input.length ∧
      (run boxed k s).base.offset.bits.length ≤ s.base.offset.bits.length + k * (16 * (L + 2609)) ∧
        (run boxed k s).rows.bits.length ≤ s.rows.bits.length + 16 * k := by
  have hb := SparseOffsetLoopControl.run_bounds boxed k s.base L hL
  rw [← run_base boxed k s] at hb
  exact ⟨hb.1, hb.2, run_row_bits boxed k s⟩

end JointThermoComplexity.Complexity.CountedSparseControl

#print axioms JointThermoComplexity.Complexity.CountedSparseControl.run_bounds
#print axioms JointThermoComplexity.Complexity.CountedSparseControl.run_rows_bound
