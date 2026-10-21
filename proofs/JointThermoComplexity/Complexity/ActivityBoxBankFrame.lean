module
public import proofs.JointThermoComplexity.Complexity.CurrentBankFrame
public import proofs.JointThermoComplexity.Complexity.BoxState

set_option autoImplicit false
@[expose] public section

/-! Positivity and rational-box work frames preserve the actual reserved production tapes. -/

namespace JointThermoComplexity.Complexity.ActivityBoxBankFrame
open _root_.Complexity
open _root_.Complexity.TM

theorem activity_frame (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : ∀ j, j ≠ MonomialPorts.species (m + 6) → work' j = work j) :
    ProductionBank.State m work → ProductionBank.State m work' := by
  intro hp j hlo hhi
  have hj : j ≠ MonomialPorts.species (m + 6) := by
    intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
  exact (hw j hj).trans (hp j hlo hhi)

theorem box_frame (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : BoxState.Unchanged (m + 5) work work') :
    ProductionBank.State m work → ProductionBank.State m work' := by
  intro hp j hlo hhi
  have he : work' j = work j := by
    apply hw j
    · intro he; have hv := congrArg Fin.val he; change j.val = 2 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 3 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 4 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 8 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
  exact he.trans (hp j hlo hhi)

theorem box_ready_and (m L idx : ℕ) (R S : (Fin (m + 20) → Tape) → Prop) (work : Fin (m + 20) → Tape) :
    BoxState.Ready (m + 5) L idx (fun work => R work ∧ S work) work ↔
      BoxState.Ready (m + 5) L idx R work ∧ S work := by
  simp only [BoxState.Ready, and_assoc]

end JointThermoComplexity.Complexity.ActivityBoxBankFrame

#print axioms JointThermoComplexity.Complexity.ActivityBoxBankFrame.activity_frame
#print axioms JointThermoComplexity.Complexity.ActivityBoxBankFrame.box_frame
#print axioms JointThermoComplexity.Complexity.ActivityBoxBankFrame.box_ready_and
