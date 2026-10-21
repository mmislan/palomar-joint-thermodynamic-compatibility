module
public import proofs.JointThermoComplexity.Complexity.OuterCurrentBankFrame
public import proofs.JointThermoComplexity.Complexity.BoxState

set_option autoImplicit false
@[expose] public section

/-! Positivity and rational-box work frames preserve the actual reserved production tapes. -/

namespace JointThermoComplexity.Complexity.OuterActivityBoxBankFrame
open _root_.Complexity
open _root_.Complexity.TM

theorem activity_frame (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : ∀ j, j ≠ MonomialPorts.species (m + 8) → work' j = work j) :
    OuterFuelBank.State m work → OuterFuelBank.State m work' := by
  intro hp j hlo hhi
  have hj : j ≠ MonomialPorts.species (m + 8) := by
    intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
  exact (hw j hj).trans (hp j hlo hhi)

theorem box_frame (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : BoxState.Unchanged (m + 7) work work') :
    OuterFuelBank.State m work → OuterFuelBank.State m work' := by
  intro hp j hlo hhi
  have he : work' j = work j := by
    apply hw j
    · intro he; have hv := congrArg Fin.val he; change j.val = 2 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 3 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 4 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 8 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
  exact he.trans (hp j hlo hhi)

theorem box_ready_and (m L idx : ℕ) (R S : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape) :
    BoxState.Ready (m + 7) L idx (fun work => R work ∧ S work) work ↔
      BoxState.Ready (m + 7) L idx R work ∧ S work := by
  simp only [BoxState.Ready, and_assoc]

end JointThermoComplexity.Complexity.OuterActivityBoxBankFrame

#print axioms JointThermoComplexity.Complexity.OuterActivityBoxBankFrame.activity_frame
#print axioms JointThermoComplexity.Complexity.OuterActivityBoxBankFrame.box_frame
#print axioms JointThermoComplexity.Complexity.OuterActivityBoxBankFrame.box_ready_and
