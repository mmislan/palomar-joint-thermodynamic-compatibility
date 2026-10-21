module
public import proofs.JointThermoComplexity.Complexity.SourceTermStep

set_option autoImplicit false
@[expose] public section

/-! Fixed-fuel control becomes inert after either rejection or a completed term forest. -/

namespace JointThermoComplexity.Complexity.SourceTermLoopState
open SourceTermToken

structure State where
  before : List Bool
  input : List Bool
  pending : ℕ
  valid : Bool
  deriving DecidableEq

def step (arity : ℕ) (s : State) : State :=
  if s.valid then match s.pending with
    | 0 => s
    | v + 1 => ⟨s.before ++ taken s.input, rest s.input,
        SourceTermStep.nextPending arity v s.input, accepted arity s.input⟩
  else s

def run (arity : ℕ) : ℕ → State → State
  | 0, s => s
  | fuel + 1, s => run arity fuel (step arity s)

def outcome (s : State) : Option (List Bool) := if s.valid && decide (s.pending = 0) then some s.input else none

@[simp] theorem run_false (arity fuel : ℕ) (before input : List Bool) (pending : ℕ) :
    run arity fuel ⟨before, input, pending, false⟩ = ⟨before, input, pending, false⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run, step, Bool.false_eq_true, ↓reduceIte] using ih

@[simp] theorem run_done (arity fuel : ℕ) (before input : List Bool) :
    run arity fuel ⟨before, input, 0, true⟩ = ⟨before, input, 0, true⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run, step, ↓reduceIte] using ih

theorem step_pending_bound (arity : ℕ) (s : State) : (step arity s).pending ≤ s.pending + 1 := by
  cases s with
  | mk before input pending valid =>
    cases valid with
    | false => simp [step]
    | true =>
      cases pending with
      | zero => simp [step]
      | succ v =>
        have hc := SourcePendingUpdate.children_bound (tagBits input)
        cases h : accepted arity input <;> simp [step, SourceTermStep.nextPending, h]
        omega

theorem step_input_bound (arity : ℕ) (s : State) : (step arity s).input.length ≤ s.input.length := by
  have he := congrArg List.length (SourceTermToken.split s.input)
  rw [List.length_append] at he
  unfold step
  split
  · cases s.pending <;> simp only <;> omega
  · exact le_rfl

theorem step_word (arity : ℕ) (s : State) : (step arity s).before ++ (step arity s).input = s.before ++ s.input := by
  unfold step
  split
  · cases s.pending <;> simp only [List.append_assoc, SourceTermToken.split]
  · rfl

theorem run_bounds (arity fuel : ℕ) (s : State) : (run arity fuel s).pending ≤ s.pending + fuel ∧
    (run arity fuel s).input.length ≤ s.input.length ∧
    (run arity fuel s).before ++ (run arity fuel s).input = s.before ++ s.input := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    obtain ⟨hp, hi, hw⟩ := ih (step arity s)
    have hs := step_pending_bound arity s
    exact ⟨by change (run arity fuel (step arity s)).pending ≤ _; omega,
      hi.trans (step_input_bound arity s), hw.trans (step_word arity s)⟩

theorem outcome_run (arity fuel pending : ℕ) (before input : List Bool) :
    outcome (run arity fuel ⟨before, input, pending, true⟩) = SourceTermControl.scan arity fuel pending input := by
  induction fuel generalizing pending before input with
  | zero => cases pending <;> simp [run, outcome, SourceTermControl.scan]
  | succ fuel ih =>
    cases pending with
    | zero => simp [SourceTermControl.scan, outcome]
    | succ v =>
      cases ha : accepted arity input with
      | false => simp [run, step, ha, SourceTermStep.nextPending, SourceTermControl.scan, outcome]
      | true =>
        simpa only [run, step, ↓reduceIte, SourceTermStep.nextPending, ha, SourceTermControl.scan] using
          ih (v + children (classify (tagBits input))) (before ++ taken input) (rest input)

end JointThermoComplexity.Complexity.SourceTermLoopState

#print axioms JointThermoComplexity.Complexity.SourceTermLoopState.run_bounds
#print axioms JointThermoComplexity.Complexity.SourceTermLoopState.outcome_run
