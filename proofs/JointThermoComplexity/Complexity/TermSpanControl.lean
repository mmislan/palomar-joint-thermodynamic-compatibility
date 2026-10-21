module
public import proofs.JointThermoComplexity.Complexity.SourcePendingUpdate

set_option autoImplicit false
@[expose] public section

/-! Total counted term traversal. A finished forest leaves any following suffix untouched. -/

namespace JointThermoComplexity.Complexity.TermSpanControl

structure State where
  before : List Bool
  input : List Bool
  pending : ℕ
  nodes : ℕ
  deriving DecidableEq

def children (input : List Bool) : ℕ :=
  if SourceTags.accepted input then SourceTermToken.children (SourceTermToken.classify (SourceTermToken.tagBits input)) else 0

def step (s : State) : State := match s.pending with
  | 0 => s
  | v + 1 => ⟨s.before ++ SourceTermToken.taken s.input, SourceTermToken.rest s.input, v + children s.input, s.nodes + 1⟩

def run : ℕ → State → State
  | 0, s => s
  | fuel + 1, s => run fuel (step s)

@[simp] theorem step_finished (before input : List Bool) (nodes : ℕ) :
    step ⟨before, input, 0, nodes⟩ = ⟨before, input, 0, nodes⟩ := rfl

@[simp] theorem run_finished (fuel : ℕ) (before input : List Bool) (nodes : ℕ) :
    run fuel ⟨before, input, 0, nodes⟩ = ⟨before, input, 0, nodes⟩ := by
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

theorem children_bound (input : List Bool) : children input ≤ 2 := by
  unfold children
  split
  · exact SourcePendingUpdate.children_bound _
  · omega

theorem step_bounds (s : State) :
    (step s).pending ≤ s.pending + 1 ∧ (step s).nodes ≤ s.nodes + 1 ∧
      (step s).input.length ≤ s.input.length ∧ (step s).before ++ (step s).input = s.before ++ s.input := by
  cases hp : s.pending with
  | zero => simp [step, hp]
  | succ v =>
    have hc := children_bound s.input
    have hw := congrArg List.length (SourceTermToken.split s.input)
    simp only [List.length_append] at hw
    simp only [step, hp, List.append_assoc, SourceTermToken.split]
    constructor
    · omega
    · exact ⟨le_rfl, by omega, trivial⟩

theorem run_bounds (fuel : ℕ) (s : State) :
    (run fuel s).pending ≤ s.pending + fuel ∧ (run fuel s).nodes ≤ s.nodes + fuel ∧
      (run fuel s).input.length ≤ s.input.length ∧ (run fuel s).before ++ (run fuel s).input = s.before ++ s.input := by
  induction fuel generalizing s with
  | zero => simp only [run, Nat.add_zero, le_refl, and_self]
  | succ fuel ih =>
    obtain ⟨hp, hn, hi, hw⟩ := ih (step s)
    obtain ⟨hp', hn', hi', hw'⟩ := step_bounds s
    exact ⟨by change (run fuel (step s)).pending ≤ _; omega,
      by change (run fuel (step s)).nodes ≤ _; omega, hi.trans hi', hw.trans hw'⟩

theorem children_head {n : ℕ} (h : SourceTermScan.Head n) (suffix : List Bool) :
    children (h.code ++ suffix) = h.children := by
  have ht : SourceTags.accepted (h.code ++ suffix) = true := by
    have ha := SourceTermToken.accepted_code h suffix
    unfold SourceTermToken.accepted at ha
    exact (Bool.and_eq_true_iff.mp ha).1
  simp only [children, ht, ↓reduceIte, SourceTermToken.children_code]

theorem step_head {n : ℕ} (h : SourceTermScan.Head n) (suffix before : List Bool) (v nodes : ℕ) :
    step ⟨before, h.code ++ suffix, v + 1, nodes⟩ =
      ⟨before ++ h.code, suffix, v + h.children, nodes + 1⟩ := by
  simp only [step, SourceTermToken.taken_code, SourceTermToken.rest_code, children_head]

end JointThermoComplexity.Complexity.TermSpanControl

#print axioms JointThermoComplexity.Complexity.TermSpanControl.run_bounds
#print axioms JointThermoComplexity.Complexity.TermSpanControl.step_head
