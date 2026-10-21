module
public import proofs.JointThermoComplexity.Complexity.ProductionBank

set_option autoImplicit false
@[expose] public section

/-! Seven actual blank tapes include the original production bank and two independent outer-loop fuel destinations. -/

namespace JointThermoComplexity.Complexity.OuterFuelBank
open _root_.Complexity
open _root_.Complexity.TM

def State (m : ℕ) (work : Fin (m + 22) → Tape) : Prop :=
  ∀ j, 9 ≤ j.val → j.val ≤ 15 → work j = DimensionEntry.blankRegister

theorem of_spare (m : ℕ) (work : Fin (m + 22) → Tape) (h : FreshArity.Spare (m + 14) work) : State m work := by
  intro j hlo hhi
  let i : Fin (m + 16) := ⟨j.val, by omega⟩
  have he : (NetworkParserFree.port (m + 16) i).castSucc = j := by apply Fin.ext; rfl
  rw [← he]
  exact h i (by change 2 ≤ j.val; omega)

theorem primary (m : ℕ) (work : Fin (m + 22) → Tape) (h : State m work) : ProductionBank.State (m + 2) work :=
  fun j hlo hhi => h j hlo (by omega)

theorem outer_zero (m : ℕ) (work : Fin (m + 22) → Tape) (h : State m work)
    (j : Fin (m + 22)) (hj : j.val = 14 ∨ j.val = 15) : IsReg 0 (work j) := by
  rw [h j (by omega) (by omega)]
  exact DimensionEntry.blank_register

theorem seed_frame (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : ∀ j, j ≠ PowerPorts.next (m + 9) → work' j = work j) : State m work → State m work' := by
  intro hp j hlo hhi
  have hn : j ≠ PowerPorts.next (m + 9) := by
    intro he; have hv := congrArg Fin.val he; change j.val = 2 at hv; omega
  exact (hw j hn).trans (hp j hlo hhi)

theorem network_frame (m : ℕ) (work work' : Fin (m + 22) → Tape)
    (hw : ∀ j, j ≠ PowerPorts.next (m + 9) → j ≠ PowerPorts.accumulator (m + 9) →
      j ≠ PowerPorts.power (m + 9) → j ≠ PowerBitState.flag (m + 9) → j ≠ MonomialPorts.previous (m + 8) →
      j ≠ MonomialPorts.species (m + 8) → j ≠ ReactionPorts.saved (m + 7) → work' j = work j) : State m work → State m work' := by
  intro hp j hlo hhi
  have he : work' j = work j := by
    apply hw j
    · intro he; have hv := congrArg Fin.val he; change j.val = 2 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 3 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 4 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = m + 20 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 6 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 7 at hv; omega
    · intro he; have hv := congrArg Fin.val he; change j.val = 8 at hv; omega
  exact he.trans (hp j hlo hhi)

theorem network_ready_and (m L offset size n : ℕ) (R S : (Fin (m + 22) → Tape) → Prop) (work : Fin (m + 22) → Tape) :
    NetworkEmitReady.Ready (m + 7) L offset size n (fun work => R work ∧ S work) work ↔
      NetworkEmitReady.Ready (m + 7) L offset size n R work ∧ S work := by
  simp only [NetworkEmitReady.Ready, and_assoc]

end JointThermoComplexity.Complexity.OuterFuelBank

#print axioms JointThermoComplexity.Complexity.OuterFuelBank.of_spare
#print axioms JointThermoComplexity.Complexity.OuterFuelBank.primary
#print axioms JointThermoComplexity.Complexity.OuterFuelBank.outer_zero
#print axioms JointThermoComplexity.Complexity.OuterFuelBank.network_frame
