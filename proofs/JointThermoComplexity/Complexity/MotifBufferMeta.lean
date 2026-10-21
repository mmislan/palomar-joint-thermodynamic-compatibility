module
public import proofs.JointThermoComplexity.Complexity.MotifBufferPorts
public import proofs.JointThermoComplexity.Complexity.BoxPins
public import proofs.JointThermoComplexity.Complexity.BoxRegisters

set_option autoImplicit false
@[expose] public section

/-! Retain validated dimensions, arity, verdict and bounded previous reference across motif-buffer updates. -/

namespace JointThermoComplexity.Complexity.MotifBufferMeta
open _root_.Complexity
open _root_.Complexity.TM
open MotifBufferPorts

def State (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) : Prop :=
  CurrentPins.Kept m input work ∧ BoxRegisters.State m input work

theorem unchanged (m : ℕ) (k : Fin 3) (work work' : Fin (m + 15) → Tape)
    (hw : ∀ j, j ≠ buffer m k → work' j = work j) : BoxState.Unchanged m work work' := by
  intro j hnext hacc hpower _ _
  fin_cases k
  · exact hw j hnext
  · exact hw j hacc
  · exact hw j hpower

theorem frame (m : ℕ) (input : List Bool) (k : Fin 3) (work work' : Fin (m + 15) → Tape)
    (hw : ∀ j, j ≠ buffer m k → work' j = work j) : State m input work → State m input work' := by
  rintro ⟨hk, hr⟩
  have hu := unchanged m k work work' hw
  exact ⟨BoxPins.frame m input work work' hu hk, BoxRegisters.frame m input work work' hu hr⟩

end JointThermoComplexity.Complexity.MotifBufferMeta

#print axioms JointThermoComplexity.Complexity.MotifBufferMeta.unchanged
#print axioms JointThermoComplexity.Complexity.MotifBufferMeta.frame
