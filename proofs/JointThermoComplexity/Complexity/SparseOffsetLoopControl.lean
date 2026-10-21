module
public import proofs.JointThermoComplexity.Complexity.SparseTermOffsetControl

set_option autoImplicit false
@[expose] public section

/-! Total marked-list control. Fuel is structural input length. -/

namespace JointThermoComplexity.Complexity.SparseOffsetLoopControl

structure State where
  running : Bool
  before : List Bool
  input : List Bool
  offset : ℕ

def step (boxed : Bool) (s : State) : State :=
  if s.running then
    if SourceBitRead.value s.input then
      ⟨true, (s.before ++ BooleanMachine.copied s.input) ++ SparseTermOffsetControl.taken (BooleanMachine.suffix s.input),
        SparseTermOffsetControl.rest (BooleanMachine.suffix s.input),
        s.offset + SparseTermOffsetControl.delta boxed (BooleanMachine.suffix s.input)⟩
    else ⟨false, s.before ++ BooleanMachine.copied s.input, BooleanMachine.suffix s.input, s.offset⟩
  else s

def run (boxed : Bool) : ℕ → State → State
  | 0, s => s
  | k + 1, s => run boxed k (step boxed s)

theorem run_succ_last (boxed : Bool) (k : ℕ) (s : State) :
    run boxed (k + 1) s = step boxed (run boxed k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih (step boxed s)

theorem step_split (boxed : Bool) (s : State) :
    (step boxed s).before ++ (step boxed s).input = s.before ++ s.input := by
  cases s with
  | mk running before input A =>
    cases running
    · rfl
    · cases input with
      | nil => simp [step, SourceBitRead.value, BooleanMachine.copied, BooleanMachine.suffix]
      | cons b raw =>
        cases b
        · simp [step, SourceBitRead.value, BooleanMachine.copied, BooleanMachine.suffix, List.append_assoc]
        · simp only [step, SourceBitRead.value, BooleanMachine.copied, BooleanMachine.suffix, ↓reduceIte]
          rw [List.append_assoc, SparseTermOffsetControl.split]
          exact List.append_assoc _ _ _

theorem step_length (boxed : Bool) (s : State) : (step boxed s).input.length ≤ s.input.length := by
  unfold step
  split
  · split
    · exact (SparseTermOffsetControl.rest_length _).trans (by cases s.input <;> simp [BooleanMachine.suffix])
    · cases s.input <;> simp [BooleanMachine.suffix]
  · exact le_rfl

theorem step_running_decreases (boxed : Bool) (s : State) (h : (step boxed s).running = true) :
    (step boxed s).input.length < s.input.length := by
  cases hr : s.running with
  | false => simp [step, hr] at h
  | true =>
    cases hi : s.input with
    | nil => simp [step, hr, hi, SourceBitRead.value] at h
    | cons b raw =>
      cases b
      · simp [step, hr, hi, SourceBitRead.value] at h
      · simpa only [step, hr, hi, SourceBitRead.value, BooleanMachine.suffix, BooleanMachine.copied,
          ↓reduceIte, List.length_cons] using Nat.lt_succ_of_le (SparseTermOffsetControl.rest_length raw)

theorem step_bits (boxed : Bool) (s : State) (L : ℕ) (hL : s.input.length ≤ L) :
    (step boxed s).offset.bits.length ≤ s.offset.bits.length + 16 * (L + 2609) := by
  unfold step
  split
  · split
    · exact (SparseTermOffsetControl.result_bits boxed (BooleanMachine.suffix s.input) s.offset).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left 16 (Nat.add_le_add_right
          ((show (BooleanMachine.suffix s.input).length ≤ s.input.length from by
            cases s.input <;> simp [BooleanMachine.suffix]).trans hL) 2609)) _)
    · change s.offset.bits.length ≤ s.offset.bits.length + 16 * (L + 2609)
      omega
  · omega

theorem run_bounds (boxed : Bool) (k : ℕ) (s : State) (L : ℕ) (hL : s.input.length ≤ L) :
    (run boxed k s).input.length ≤ s.input.length ∧
      (run boxed k s).offset.bits.length ≤ s.offset.bits.length + k * (16 * (L + 2609)) := by
  induction k generalizing s with
  | zero => simp only [run, Nat.zero_mul, Nat.add_zero, le_refl, and_self]
  | succ k ih =>
    have hs := step_length boxed s
    have hi := ih (step boxed s) (hs.trans hL)
    refine ⟨hi.1.trans hs, ?_⟩
    have hb := step_bits boxed s L hL
    change (run boxed k (step boxed s)).offset.bits.length ≤ _
    calc
      _ ≤ (step boxed s).offset.bits.length + k * (16 * (L + 2609)) := hi.2
      _ ≤ s.offset.bits.length + 16 * (L + 2609) + k * (16 * (L + 2609)) := Nat.add_le_add_right hb _
      _ = _ := by rw [Nat.add_mul]; omega

theorem run_stopped (boxed : Bool) (k : ℕ) (s : State) (hs : s.running = false) : run boxed k s = s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [run, step, hs, Bool.false_eq_true, ↓reduceIte] using ih

theorem run_stops (boxed : Bool) (k : ℕ) (s : State) (h : s.input.length < k) :
    (run boxed k s).running = false := by
  induction k generalizing s with
  | zero => omega
  | succ k ih =>
    by_cases hs : (step boxed s).running = true
    · have hd := step_running_decreases boxed s hs
      exact ih (step boxed s) (by omega)
    · have hf : (step boxed s).running = false := by simpa using hs
      simpa only [run, run_stopped boxed k (step boxed s) hf] using hf

end JointThermoComplexity.Complexity.SparseOffsetLoopControl

#print axioms JointThermoComplexity.Complexity.SparseOffsetLoopControl.run_bounds
#print axioms JointThermoComplexity.Complexity.SparseOffsetLoopControl.run_stops
