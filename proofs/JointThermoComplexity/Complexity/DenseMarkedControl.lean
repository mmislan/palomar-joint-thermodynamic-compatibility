module
public import proofs.JointThermoComplexity.Complexity.DenseLoadedPacket
public import proofs.JointThermoComplexity.Complexity.CountedSparseControl

set_option autoImplicit false
@[expose] public section

/-! The old total raw cursor/count control also indexes emitted record words.
Its offset field is a ghost and is not a physical source-pass accumulator. -/

namespace JointThermoComplexity.Complexity.DenseMarkedControl
open CountedSparseControl

def word (boxed right : Bool) (n N : ℕ) (s : State) : List Bool :=
  if s.base.running then
    if SourceBitRead.value s.base.input then DenseLoadedPacket.word boxed right n N (2 + s.rows) (BooleanMachine.suffix s.base.input)
    else []
  else []
def runWords (boxed right : Bool) (n N : ℕ) : ℕ → State → List Bool
  | 0, _ => []
  | k + 1, s => word boxed right n N s ++ runWords boxed right n N k (step boxed s)

theorem runWords_succ_last (boxed right : Bool) (n N k : ℕ) (s : State) :
    runWords boxed right n N (k + 1) s = runWords boxed right n N k s ++ word boxed right n N (run boxed k s) := by
  induction k generalizing s with
  | zero => simp only [runWords, run, List.nil_append, List.append_nil]
  | succ k ih =>
    change word boxed right n N s ++ runWords boxed right n N (k + 1) (step boxed s) =
      (word boxed right n N s ++ runWords boxed right n N k (step boxed s)) ++ word boxed right n N (run boxed k (step boxed s))
    rw [ih (step boxed s), List.append_assoc]

theorem run_add (boxed : Bool) (a b : ℕ) (s : State) : run boxed (a + b) s = run boxed b (run boxed a s) := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add, run]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    exact ih (step boxed s)

theorem rows_le_step (boxed : Bool) (s : State) : s.rows ≤ (step boxed s).rows := by
  change s.rows ≤ s.rows + increment s
  omega
theorem rows_le_run (boxed : Bool) (k : ℕ) (s : State) : s.rows ≤ (run boxed k s).rows := by
  induction k generalizing s with
  | zero => exact le_rfl
  | succ k ih => exact (rows_le_step boxed s).trans (ih (step boxed s))
theorem run_rows_mono (boxed : Bool) (a b : ℕ) (s : State) (hab : a ≤ b) : (run boxed a s).rows ≤ (run boxed b s).rows := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hab
  rw [hd, run_add]
  exact rows_le_run boxed d (run boxed a s)
theorem next_rows_le_final (boxed : Bool) (count i : ℕ) (s : State) (hi : i < count) :
    (step boxed (run boxed i s)).rows ≤ (run boxed count s).rows := by
  rw [← run_succ_last]
  exact run_rows_mono boxed (i + 1) count s (by omega)

theorem step_fit (boxed : Bool) (s : State) (N : ℕ) (hN : (step boxed s).rows ≤ N)
    (hrun : s.base.running = true) (hmarker : SourceBitRead.value s.base.input = true) :
    2 + s.rows + SparseTermOffsetControl.count (BooleanMachine.suffix s.base.input) ≤ N + 2 := by
  simpa only [step, increment, hrun, hmarker, ↓reduceIte, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Nat.add_le_add_left hN 2

end JointThermoComplexity.Complexity.DenseMarkedControl

#print axioms JointThermoComplexity.Complexity.DenseMarkedControl.runWords_succ_last
#print axioms JointThermoComplexity.Complexity.DenseMarkedControl.next_rows_le_final
