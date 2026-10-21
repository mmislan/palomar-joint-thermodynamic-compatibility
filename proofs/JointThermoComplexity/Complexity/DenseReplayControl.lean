module
public import proofs.JointThermoComplexity.Complexity.SparseDenseRescan

set_option autoImplicit false
@[expose] public section

/-! Replaying the source preserves counted rows independently of the unused
ghost offset. Global raw bit budgets follow from the original counted pass. -/

namespace JointThermoComplexity.Complexity.DenseReplayControl
open CountedSparseControl (State)

def Same (s t : State) : Prop := s.base.running = t.base.running ∧ s.base.before = t.base.before ∧
  s.base.input = t.base.input ∧ s.rows = t.rows

theorem step_same (boxed : Bool) (s t : State) (h : Same s t) : Same (CountedSparseControl.step boxed s) (CountedSparseControl.step boxed t) := by
  rcases s with ⟨⟨running, before, input, A⟩, rows⟩
  rcases t with ⟨⟨running', before', input', A'⟩, rows'⟩
  rcases h with ⟨rfl, rfl, rfl, rfl⟩
  cases running <;> cases hv : SourceBitRead.value input <;>
    simp only [Same, CountedSparseControl.step, CountedSparseControl.increment, SparseOffsetLoopControl.step, hv,
      Bool.false_eq_true, ↓reduceIte, and_self]

theorem run_same (boxed : Bool) (k : ℕ) (s t : State) (h : Same s t) :
    Same (CountedSparseControl.run boxed k s) (CountedSparseControl.run boxed k t) := by
  induction k generalizing s t with
  | zero => exact h
  | succ k ih => exact ih _ _ (step_same boxed s t h)

def rescan (boxed : Bool) (input : List Bool) : State :=
  SparseDenseRescan.outcome (SparseDimensionRewind.restart (SparseDimensionEntry.outcome boxed input) input)
def state (boxed : Bool) (input : List Bool) : State := ⟨(rescan boxed input).base, 0⟩
def budget (L : ℕ) : ℕ := 16 * L + 3 + L * (16 * (L + 2609))

theorem state_same (boxed : Bool) (input : List Bool) : Same (state boxed input) (SparseCountedEntry.state input) := by
  simp only [Same, state, rescan, SparseDenseRescan.outcome, SparseDenseRescan.activated,
    SparseDenseRescan.skipped, SparseDimensionRewind.restart, SparseCountedEntry.state, List.nil_append, and_self]

theorem run_rows (boxed : Bool) (input : List Bool) :
    (CountedSparseControl.run boxed input.length (state boxed input)).rows = (SparseDimensionEntry.outcome boxed input).rows :=
  (run_same boxed input.length _ _ (state_same boxed input)).2.2.2

theorem rescan_rows (boxed : Bool) (input : List Bool) : (rescan boxed input).rows = (SparseDimensionEntry.outcome boxed input).rows := rfl

theorem input_length (boxed : Bool) (input : List Bool) : (state boxed input).base.input.length ≤ input.length := by
  change (HeaderControl.suffix input).length ≤ input.length
  have h := congrArg List.length (HeaderControl.consumed_and_suffix input)
  rw [List.length_append] at h
  omega

theorem length_le_budget (L : ℕ) : L ≤ budget L := by unfold budget; omega
theorem rows_le_budget (boxed : Bool) (input : List Bool) : (rescan boxed input).rows + 2 ≤ budget input.length := by
  have h := SparseDimensionEntry.rows_bound boxed input
  rw [← rescan_rows boxed input] at h
  unfold budget
  omega
theorem count_bits_le_budget (boxed : Bool) (input : List Bool) : (rescan boxed input).rows.bits.length ≤ budget input.length :=
  (BoundedUnaryControl.bits_le _).trans (by have h := rows_le_budget boxed input; omega)

theorem offset_bits_le_budget (boxed : Bool) (input : List Bool) : (rescan boxed input).base.offset.bits.length ≤ budget input.length := by
  have hlen : (SparseCountedEntry.state input).base.input.length ≤ input.length := (state_same boxed input).2.2.1 ▸ input_length boxed input
  have h := (CountedSparseControl.run_bounds boxed input.length (SparseCountedEntry.state input) input.length hlen).2.1
  have hone : (SparseCountedEntry.state input).base.offset.bits.length = 1 := by
    change (1 : ℕ).bits.length = 1
    decide
  rw [hone] at h
  change (rescan boxed input).base.offset.bits.length ≤ 1 + input.length * (16 * (input.length + 2609)) at h
  unfold budget
  omega

end JointThermoComplexity.Complexity.DenseReplayControl

#print axioms JointThermoComplexity.Complexity.DenseReplayControl.run_rows
#print axioms JointThermoComplexity.Complexity.DenseReplayControl.offset_bits_le_budget
