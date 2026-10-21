module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxToken

set_option autoImplicit false
@[expose] public section

/-! Total bounded streaming state, independent of any typed proof or syntax-tree witness. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxControl

structure State where
  before : List Bool
  input : List Bool
  emitted : List Bool
  pending : ℕ
  deriving DecidableEq

def step (s : State) : State :=
  let next := SmallSyntaxToken.step s.pending s.input
  ⟨s.before ++ next.taken, next.rest, s.emitted ++ next.output, next.pending⟩

def run : ℕ → State → State
  | 0, s => s
  | fuel + 1, s => run fuel (step s)

@[simp] theorem step_empty (before emitted : List Bool) (pending : ℕ) :
    step ⟨before, [], emitted, pending⟩ = ⟨before, [], emitted, pending⟩ := by
  simp only [step, SmallSyntaxToken.step_empty, List.append_nil]

@[simp] theorem run_empty (fuel : ℕ) (before emitted : List Bool) (pending : ℕ) :
    run fuel ⟨before, [], emitted, pending⟩ = ⟨before, [], emitted, pending⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run, step_empty] using ih

theorem run_add (a b : ℕ) (s : State) : run (a + b) s = run b (run a s) := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add, run]
  | succ a ih => simpa only [Nat.succ_add, run] using ih (step s)

theorem run_succ_last (fuel : ℕ) (s : State) : run (fuel + 1) s = step (run fuel s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih => exact ih (step s)

theorem step_word (s : State) : (step s).before ++ (step s).input = s.before ++ s.input := by
  simp only [step, List.append_assoc, SmallSyntaxToken.split]

theorem run_bounds (fuel : ℕ) (s : State) :
    (run fuel s).pending ≤ s.pending + 2 * fuel ∧ (run fuel s).input.length ≤ s.input.length ∧
      (run fuel s).before ++ (run fuel s).input = s.before ++ s.input := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    obtain ⟨hp, hi, hw⟩ := ih (step s)
    have hs := SmallSyntaxToken.pending_bound s.pending s.input
    refine ⟨?_, hi.trans (SmallSyntaxToken.input_bound s.pending s.input), hw.trans (step_word s)⟩
    change (run fuel (step s)).pending ≤ s.pending + 2 * (fuel + 1)
    change (run fuel (step s)).pending ≤ (SmallSyntaxToken.step s.pending s.input).pending + 2 * fuel at hp
    omega

def code (input : List Bool) : List Bool :=
  (run input.length ⟨HeaderControl.copied input, HeaderControl.suffix input, HeaderControl.copied input, 0⟩).emitted

end JointThermoComplexity.Complexity.SmallSyntaxControl

#print axioms JointThermoComplexity.Complexity.SmallSyntaxControl.run_bounds
#print axioms JointThermoComplexity.Complexity.SmallSyntaxControl.run_add
