module
public import proofs.JointThermoComplexity.Complexity.SparseDimensionEntry

set_option autoImplicit false
@[expose] public section

/-! The complete raw first pass retains the original word under its cursor. -/

namespace JointThermoComplexity.Complexity.SparseSourceWord

theorem run_word (boxed : Bool) (k : ℕ) (s : SparseOffsetLoopControl.State) :
    (SparseOffsetLoopControl.run boxed k s).before ++ (SparseOffsetLoopControl.run boxed k s).input = s.before ++ s.input := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact (ih (SparseOffsetLoopControl.step boxed s)).trans (SparseOffsetLoopControl.step_split boxed s)

theorem outcome_word (boxed : Bool) (input : List Bool) :
    (SparseDimensionEntry.outcome boxed input).base.before ++ (SparseDimensionEntry.outcome boxed input).base.input = input := by
  unfold SparseDimensionEntry.outcome
  rw [CountedSparseControl.run_base]
  exact (run_word boxed input.length (SparseCountedEntry.state input).base).trans (HeaderControl.consumed_and_suffix input)

theorem outcome_before_length (boxed : Bool) (input : List Bool) :
    (SparseDimensionEntry.outcome boxed input).base.before.length ≤ input.length := by
  have he := congrArg List.length (outcome_word boxed input)
  rw [List.length_append] at he
  omega

end JointThermoComplexity.Complexity.SparseSourceWord

#print axioms JointThermoComplexity.Complexity.SparseSourceWord.outcome_word
