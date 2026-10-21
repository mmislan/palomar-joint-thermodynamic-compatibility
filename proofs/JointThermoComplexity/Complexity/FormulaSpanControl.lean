module
public import proofs.JointThermoComplexity.Complexity.TermSpanLoop
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxForests
public import proofs.JointThermoComplexity.Complexity.SourceCoordinateEnumeration

set_option autoImplicit false
@[expose] public section

/-! Total mixed traversal counts the exact allocated coordinates, including all three atomic witness slots. -/

namespace JointThermoComplexity.Complexity.FormulaSpanControl

structure State where
  before : List Bool
  input : List Bool
  terms : ℕ
  formulas : ℕ
  coordinates : ℕ
  deriving DecidableEq

def termState (s : State) : TermSpanControl.State := ⟨s.before, s.input, s.terms, s.coordinates⟩
def fromTerm (formulas : ℕ) (s : TermSpanControl.State) : State := ⟨s.before, s.input, s.pending, formulas, s.nodes⟩

def termCount (bits : List Bool) : ℕ := match SourceFormulaScan.classify bits with
  | .eq | .lt => 2
  | _ => 0

def allocation (bits : List Bool) : ℕ := match SourceFormulaScan.classify bits with
  | .eq | .lt => 4
  | _ => 1

def formulaStep (v : ℕ) (s : State) : State :=
  let bits := SourceTermToken.tagBits s.input
  let present := SourceTags.accepted s.input
  ⟨s.before ++ s.input.take 3, s.input.drop 3, if present then termCount bits else 0,
    v + if present then (SourceFormulaScan.classify bits).children else 0,
    s.coordinates + if present then allocation bits else 1⟩

def step (s : State) : State := match s.terms, s.formulas with
  | 0, 0 => s
  | 0, v + 1 => formulaStep v s
  | _ + 1, _ => fromTerm s.formulas (TermSpanControl.step (termState s))

def run : ℕ → State → State
  | 0, s => s
  | fuel + 1, s => run fuel (step s)

@[simp] theorem step_finished (before input : List Bool) (coordinates : ℕ) :
    step ⟨before, input, 0, 0, coordinates⟩ = ⟨before, input, 0, 0, coordinates⟩ := rfl

@[simp] theorem run_finished (fuel : ℕ) (before input : List Bool) (coordinates : ℕ) :
    run fuel ⟨before, input, 0, 0, coordinates⟩ = ⟨before, input, 0, 0, coordinates⟩ := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [run, step_finished] using ih

theorem run_add (a b : ℕ) (s : State) : run (a + b) s = run b (run a s) := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add, run]
  | succ a ih => simpa only [Nat.succ_add, run] using ih (step s)

theorem run_succ_last (fuel : ℕ) (s : State) : run (fuel + 1) s = step (run fuel s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih => exact ih (step s)

theorem termCount_bound (bits : List Bool) : termCount bits ≤ 2 := by
  cases hk : SourceFormulaScan.classify bits <;> simp [termCount, hk]

theorem allocation_bound (bits : List Bool) : allocation bits ≤ 4 := by
  cases hk : SourceFormulaScan.classify bits <;> simp [allocation, hk]

theorem step_bounds (s : State) :
    (step s).terms ≤ s.terms + 2 ∧ (step s).formulas ≤ s.formulas + 1 ∧
      (step s).coordinates ≤ s.coordinates + 4 ∧ (step s).input.length ≤ s.input.length ∧
      (step s).before ++ (step s).input = s.before ++ s.input := by
  cases ht : s.terms with
  | zero =>
    cases hf : s.formulas with
    | zero => simp [step, ht, hf]
    | succ v =>
      have hc := termCount_bound (SourceTermToken.tagBits s.input)
      have ha := allocation_bound (SourceTermToken.tagBits s.input)
      have hf' := SourceFormulaScan.children_bound (SourceTermToken.tagBits s.input)
      have hw := List.take_append_drop 3 s.input
      have hlen : (s.input.drop 3).length ≤ s.input.length := by simp only [List.length_drop]; omega
      simp only [step, ht, hf, formulaStep]
      refine ⟨?_, ?_, ?_, hlen, ?_⟩
      · split <;> omega
      · split <;> omega
      · split <;> omega
      · simp only [List.append_assoc, hw]
  | succ v =>
    have hb := TermSpanControl.step_bounds (termState s)
    simp only [step, ht, fromTerm]
    refine ⟨?_, ?_, ?_, hb.2.2.1, hb.2.2.2⟩
    · have h := hb.1
      change (TermSpanControl.step (termState s)).pending ≤ s.terms + 1 at h
      omega
    · omega
    · have h := hb.2.1
      change (TermSpanControl.step (termState s)).nodes ≤ s.coordinates + 4
      change (TermSpanControl.step (termState s)).nodes ≤ s.coordinates + 1 at h
      omega

theorem run_bounds (fuel : ℕ) (s : State) :
    (run fuel s).terms ≤ s.terms + 2 * fuel ∧ (run fuel s).formulas ≤ s.formulas + fuel ∧
      (run fuel s).coordinates ≤ s.coordinates + 4 * fuel ∧ (run fuel s).input.length ≤ s.input.length ∧
      (run fuel s).before ++ (run fuel s).input = s.before ++ s.input := by
  induction fuel generalizing s with
  | zero => simp only [run, Nat.mul_zero, Nat.add_zero, le_refl, and_self]
  | succ fuel ih =>
    obtain ⟨ht, hf, hc, hi, hw⟩ := ih (step s)
    obtain ⟨ht', hf', hc', hi', hw'⟩ := step_bounds s
    refine ⟨?_, ?_, ?_, hi.trans hi', hw.trans hw'⟩
    · change (run fuel (step s)).terms ≤ _; omega
    · change (run fuel (step s)).formulas ≤ _; omega
    · change (run fuel (step s)).coordinates ≤ _; omega

end JointThermoComplexity.Complexity.FormulaSpanControl

#print axioms JointThermoComplexity.Complexity.FormulaSpanControl.step_bounds
#print axioms JointThermoComplexity.Complexity.FormulaSpanControl.run_bounds
