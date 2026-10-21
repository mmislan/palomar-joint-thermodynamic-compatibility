module
public import proofs.JointThermoComplexity.Complexity.ProductionPorts

set_option autoImplicit false
@[expose] public section

/-! The five future production tapes stay exactly blank under circuit-prefix work frames. -/

namespace JointThermoComplexity.Complexity.ProductionBank
open _root_.Complexity
open _root_.Complexity.TM

def State (m : ℕ) (work : Fin (m + 20) → Tape) : Prop :=
  ∀ j, 9 ≤ j.val → j.val ≤ 13 → work j = DimensionEntry.blankRegister

theorem of_spare (m : ℕ) (work : Fin (m + 20) → Tape) (h : FreshArity.Spare (m + 12) work) : State m work :=
  fun j hlo hhi => ProductionPorts.reserved_blank m work h j hlo hhi

theorem seed_frame (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : ∀ j, j ≠ PowerPorts.next (m + 7) → work' j = work j) : State m work → State m work' := by
  intro hp j hlo hhi
  have hn : j ≠ PowerPorts.next (m + 7) := by
    intro he; have hv := congrArg Fin.val he; change j.val = 2 at hv; omega
  exact (hw j hn).trans (hp j hlo hhi)

theorem network_frame (m : ℕ) (work work' : Fin (m + 20) → Tape)
    (hw : ∀ j, j ≠ PowerPorts.next (m + 7) → j ≠ PowerPorts.accumulator (m + 7) →
      j ≠ PowerPorts.power (m + 7) → j ≠ PowerBitState.flag (m + 7) → j ≠ MonomialPorts.previous (m + 6) →
      j ≠ MonomialPorts.species (m + 6) → j ≠ ReactionPorts.saved (m + 5) → work' j = work j) : State m work → State m work' := by
  intro hp j hlo hhi
  have he : work' j = work j := by
    apply hw j
    · intro he; have hv := congrArg Fin.val he; change j.val = 2 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 3 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 4 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = m + 18 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 6 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 8 at hv; omega
  exact he.trans (hp j hlo hhi)

theorem network_ready_and (m L offset size n : ℕ) (R S : (Fin (m + 20) → Tape) → Prop) (work : Fin (m + 20) → Tape) :
    NetworkEmitReady.Ready (m + 5) L offset size n (fun work => R work ∧ S work) work ↔
      NetworkEmitReady.Ready (m + 5) L offset size n R work ∧ S work := by
  simp only [NetworkEmitReady.Ready, and_assoc]

end JointThermoComplexity.Complexity.ProductionBank

#print axioms JointThermoComplexity.Complexity.ProductionBank.network_frame
#print axioms JointThermoComplexity.Complexity.ProductionBank.network_ready_and
