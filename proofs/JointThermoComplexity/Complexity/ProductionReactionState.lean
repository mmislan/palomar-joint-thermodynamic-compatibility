module
public import proofs.JointThermoComplexity.Complexity.ProductionSelectedTerm

set_option autoImplicit false
@[expose] public section

/-! Actual arithmetic resources, bounded indices and a reaction-mask cursor form the production iteration invariant. -/

namespace JointThermoComplexity.Complexity.ProductionReactionState
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts

def State (m L n ri si idx : ℕ) (mask : List Bool) (k : ℕ)
    (R : (Fin (m + 20) → Tape) → Prop) (work : Fin (m + 20) → Tape) : Prop :=
  ProductionOperandLoad.State m L n ri si work ∧ IsReg idx (work (current m)) ∧
    BinaryIncrementRun.Register 0 (work (PowerPorts.scratch (m + 7))) ∧
    MotifDirectionState.At mask k (work (MotifBufferPorts.buffer (m + 5) 1)) ∧ R work

def Unchanged (m : ℕ) (work work' : Fin (m + 20) → Tape) : Prop :=
  ∀ j, j ≠ MotifBufferPorts.buffer (m + 5) 1 → j ≠ PowerPorts.scratch (m + 7) →
    j ≠ reaction m → j ≠ current m → j ≠ magnitude m → j ≠ left m → j ≠ right m → j ≠ sign m → work' j = work j

theorem of_term (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : ProductionTermFrame.Unchanged m work work') : Unchanged m work work' :=
  fun j _ hz _ hc hm hl hr hs => hw j hl hr hs hm hc hz

theorem of_reaction (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : ∀ j, j ≠ reaction m → work' j = work j) : Unchanged m work work' :=
  fun j _ _ hj _ _ _ _ _ => hw j hj

theorem of_current (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : ∀ j, j ≠ current m → work' j = work j) : Unchanged m work work' :=
  fun j _ _ _ hj _ _ _ _ => hw j hj

theorem of_mask (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : ∀ j, j ≠ MotifBufferPorts.buffer (m + 5) 1 → work' j = work j) : Unchanged m work work' :=
  fun j hj _ _ _ _ _ _ _ => hw j hj

theorem map_state (m L n ri si idx : ℕ) (mask : List Bool) (k : ℕ)
    (R S : (Fin (m + 20) → Tape) → Prop) (work : Fin (m + 20) → Tape)
    (h : R work → S work) (hp : State m L n ri si idx mask k R work) : State m L n ri si idx mask k S work :=
  ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, h hp.2.2.2.2⟩

end JointThermoComplexity.Complexity.ProductionReactionState

#print axioms JointThermoComplexity.Complexity.ProductionReactionState.of_term
#print axioms JointThermoComplexity.Complexity.ProductionReactionState.map_state
