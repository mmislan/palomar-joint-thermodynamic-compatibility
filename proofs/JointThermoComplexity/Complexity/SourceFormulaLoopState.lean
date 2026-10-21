module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaStep

set_option autoImplicit false
@[expose] public section

/-! Fixed-fuel formula control is inert after rejection or completion of the pending forest. -/

namespace JointThermoComplexity.Complexity.SourceFormulaLoopState
open SourceTermLoopState (State outcome)

def step (arity L : ℕ) (s : State) : State :=
  if s.valid then match s.pending with
    | 0 => s
    | v + 1 => SourceFormulaStep.afterStep arity L v s.before s.input
  else s

def run (arity L : ℕ) : ℕ → State → State
  | 0, s => s
  | fuel + 1, s => run arity L fuel (step arity L s)

@[simp] theorem run_false (arity L fuel : ℕ) (before input : List Bool) (pending : ℕ) :
    run arity L fuel ⟨before, input, pending, false⟩ = ⟨before, input, pending, false⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run, step, Bool.false_eq_true, ↓reduceIte] using ih

@[simp] theorem run_done (arity L fuel : ℕ) (before input : List Bool) :
    run arity L fuel ⟨before, input, 0, true⟩ = ⟨before, input, 0, true⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run, step, ↓reduceIte] using ih

theorem step_pending_bound (arity L : ℕ) (s : State) : (step arity L s).pending ≤ s.pending + 1 := by
  cases s with
  | mk before input pending valid =>
    cases valid with
    | false => simp [step]
    | true =>
      cases pending with
      | zero => simp [step]
      | succ v =>
        have hc := SourceFormulaScan.children_bound (SourceTermToken.tagBits input)
        cases h : SourceFormulaToken.accepted arity L input <;> simp [step, SourceFormulaStep.afterStep, h]
        omega

theorem step_input_bound (arity L : ℕ) (s : State) : (step arity L s).input.length ≤ s.input.length := by
  have he := congrArg List.length (SourceFormulaToken.split arity L s.input)
  rw [List.length_append] at he
  unfold step
  split
  · cases s.pending <;> simp only [SourceFormulaStep.afterStep] <;> omega
  · exact le_rfl

theorem step_word (arity L : ℕ) (s : State) :
    (step arity L s).before ++ (step arity L s).input = s.before ++ s.input := by
  unfold step
  split
  · cases s.pending <;> simp only [SourceFormulaStep.afterStep, List.append_assoc, SourceFormulaToken.split]
  · rfl

theorem run_bounds (arity L fuel : ℕ) (s : State) : (run arity L fuel s).pending ≤ s.pending + fuel ∧
    (run arity L fuel s).input.length ≤ s.input.length ∧
    (run arity L fuel s).before ++ (run arity L fuel s).input = s.before ++ s.input := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    obtain ⟨hp, hi, hw⟩ := ih (step arity L s)
    have hs := step_pending_bound arity L s
    exact ⟨by change (run arity L fuel (step arity L s)).pending ≤ _; omega,
      hi.trans (step_input_bound arity L s), hw.trans (step_word arity L s)⟩

theorem outcome_run (arity L fuel pending : ℕ) (before input : List Bool) :
    outcome (run arity L fuel ⟨before, input, pending, true⟩) = SourceFormulaScan.scan arity L fuel pending input := by
  induction fuel generalizing pending before input with
  | zero => cases pending <;> simp [run, outcome, SourceFormulaScan.scan]
  | succ fuel ih =>
    cases pending with
    | zero => simp [SourceFormulaScan.scan, outcome]
    | succ v =>
      cases ha : SourceFormulaToken.accepted arity L input with
      | false => simp [run, step, ha, SourceFormulaStep.afterStep, SourceFormulaScan.scan, outcome]
      | true =>
        simpa only [run, step, ↓reduceIte, SourceFormulaStep.afterStep, ha, SourceFormulaScan.scan] using
          ih (v + (SourceFormulaScan.classify (SourceTermToken.tagBits input)).children)
            (before ++ SourceFormulaToken.taken arity L input) (SourceFormulaToken.rest arity L input)

end JointThermoComplexity.Complexity.SourceFormulaLoopState

#print axioms JointThermoComplexity.Complexity.SourceFormulaLoopState.run_bounds
#print axioms JointThermoComplexity.Complexity.SourceFormulaLoopState.outcome_run
