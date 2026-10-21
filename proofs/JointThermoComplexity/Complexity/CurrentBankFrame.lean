module
public import proofs.JointThermoComplexity.Complexity.ProductionBank
public import proofs.JointThermoComplexity.Complexity.CurrentReady

set_option autoImplicit false
@[expose] public section

/-! Current initialization and equation emission leave the reserved production bank untouched. -/

namespace JointThermoComplexity.Complexity.CurrentBankFrame
open _root_.Complexity
open _root_.Complexity.TM

theorem start_frame (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : ∀ j, j ≠ CurrentPorts.raw (m + 5) → j ≠ MonomialPorts.species (m + 6) → work' j = work j) :
    ProductionBank.State m work → ProductionBank.State m work' := by
  intro hp j hlo hhi
  have hraw : j ≠ CurrentPorts.raw (m + 5) := by
    intro he; have hv := congrArg Fin.val he; change j.val = m + 19 at hv; omega
  have hcurrent : j ≠ MonomialPorts.species (m + 6) := by
    intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
  exact (hw j hraw hcurrent).trans (hp j hlo hhi)

theorem build_frame (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : ∀ j, j ≠ CurrentPorts.raw (m + 5) → j ≠ MonomialPorts.previous (m + 6) →
      j ≠ MonomialPorts.species (m + 6) → work' j = work j) :
    ProductionBank.State m work → ProductionBank.State m work' := by
  intro hp j hlo hhi
  have hraw : j ≠ CurrentPorts.raw (m + 5) := by
    intro he; have hv := congrArg Fin.val he; change j.val = m + 19 at hv; omega
  have hprevious : j ≠ MonomialPorts.previous (m + 6) := by
    intro he; have hv := congrArg Fin.val he; change j.val = 6 at hv; omega
  have hcurrent : j ≠ MonomialPorts.species (m + 6) := by
    intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
  exact (hw j hraw hprevious hcurrent).trans (hp j hlo hhi)

theorem ready_and (m L count idx n : ℕ) (R S : (Fin (m + 20) → Tape) → Prop) (work : Fin (m + 20) → Tape) :
    CurrentReady.Ready (m + 5) L count idx n (fun work => R work ∧ S work) work ↔
      CurrentReady.Ready (m + 5) L count idx n R work ∧ S work := by
  simp only [CurrentReady.Ready, and_assoc]

end JointThermoComplexity.Complexity.CurrentBankFrame

#print axioms JointThermoComplexity.Complexity.CurrentBankFrame.build_frame
#print axioms JointThermoComplexity.Complexity.CurrentBankFrame.ready_and
