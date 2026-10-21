module
public import proofs.JointThermoComplexity.Complexity.DenseTwoPassControl

set_option autoImplicit false
@[expose] public section

/-! Actual complete left/right reaction lists on every raw source word. -/

namespace JointThermoComplexity.Complexity.DenseTwoPass
open _root_.Complexity _root_.Complexity.TM HeaderAt
open DenseTwoPassControl

def branchWord (boxed right : Bool) (input : List Bool) : List Bool :=
  DenseBranchPass.word boxed right (arity input) (total boxed input) (offset boxed input) input.length (initial boxed input)
def leftWord (boxed : Bool) (input : List Bool) : List Bool :=
  SparseDimensionWords.header boxed (arity input) (total boxed input) ++ branchWord boxed false input
def word (boxed : Bool) (input : List Bool) : List Bool := leftWord boxed input ++ branchWord boxed true input
def machine (boxed : Bool) : TM 64 :=
  seqTM (DenseBranchPass.entry boxed false) (seqTM DenseSourceRestart.machine (DenseBranchPass.machine boxed true))
def timeBound (boxed : Bool) (input : List Bool) : ℕ :=
  DenseBranchPass.entryBound boxed false input + 1 + (restartBound input.length + 1 +
    DenseBranchPass.timeBound boxed true input.length (arity input) (total boxed input) (DenseReplayControl.budget input.length) input.length)

theorem hoareTime (boxed : Bool) (input : List Bool) :
    (machine boxed).HoareTime (InitialTapeLift.Initial 64 input) (Payload boxed input (word boxed input)) (timeBound boxed input) := by
  have h1 : (DenseBranchPass.entry boxed false).HoareTime (InitialTapeLift.Initial 64 input)
      (Payload boxed input (leftWord boxed input)) (DenseBranchPass.entryBound boxed false input) :=
    DenseBranchPass.entry_hoareTime boxed false input
  have h2 := restart_hoareTime boxed input (leftWord boxed input)
  have h3 := branch_hoareTime boxed true input (leftWord boxed input)
  have h23 := seqTM_hoareTime _ _ h2 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.1.phase
    rw [hi, hw, ho]
    exact h) h3
  exact seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.1.phase
    rw [hi, hw, ho]
    exact h) h23

end JointThermoComplexity.Complexity.DenseTwoPass

#print axioms JointThermoComplexity.Complexity.DenseTwoPass.hoareTime
