module
public import proofs.JointThermoComplexity.Complexity.FormulaEquationBranch

set_option autoImplicit false
@[expose] public section

/-! Boolean tag/flag writes preserve the independent query and address state. -/

namespace JointThermoComplexity.Complexity.BranchWorkTransfer
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryWorkFrame QueryCounterInit LocalBranchState
open HeaderAt (Cursor)

def Outside (j : Fin 32) : Prop := (∀ i, j ≠ tags i) ∧ j ≠ flag ∧ j ≠ anchor

theorem protected_outside : ∀ j, Protected j → Outside j := by
  unfold Protected Outside
  decide

theorem slot_outside (i : Fin 9) : Outside (AddressCounterPlacement.slot i) := by
  refine ⟨?_, ?_, slot_anchor i⟩
  · intro k he
    have hv := congrArg Fin.val he
    change 19 + i.val = k.val + 8 at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    change 19 + i.val = 14 at hv
    omega

theorem transfer (counts : Counts) (values : Fin 9 → ℕ) (L : ℕ) (R : Work → Prop)
    (hR : LocalBranchState.Stable R) (work work' : Work) (hr : Ready counts values L R work)
    (he : ∀ j, Outside j → work' j = work j)
    (ht : ∀ i, (work' (tags i)).head = 1) (hf : (work' flag).head = 1)
    (hm : ∀ j, j ≠ anchor → (work' j).cells 0 = Γ.start) : Ready counts values L R work' := by
  refine ⟨⟨ht, hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hm, ?_⟩
  · simpa only [he _ (by unfold Outside; decide : Outside pending)] using hr.basic.termReg
  · simpa only [he _ (by unfold Outside; decide : Outside formulas)] using hr.basic.formulaReg
  · simpa only [he _ (by unfold Outside; decide : Outside result)] using hr.basic.nodeReg
  · simpa only [he _ (by unfold Outside; decide : Outside fuel)] using hr.basic.fuelReg
  · simpa only [he _ (by unfold Outside; decide : Outside position)] using hr.basic.positionReg
  · simpa only [he _ (by unfold Outside; decide : Outside scratch)] using hr.basic.scratchReg
  · exact hR work work' (fun j hj => he j (protected_outside j hj)) hr.basic.frame
  · intro i
    simpa only [he _ (slot_outside i)] using hr.addresses i

theorem full_markers (counts : Counts) (values : Fin 9 → ℕ) (L p : ℕ) (R : Work → Prop) (work : Work)
    (hr : Ready counts values L R work) (hp : IsReg p (work anchor)) : ∀ j, (work j).cells 0 = Γ.start := by
  intro j
  by_cases hj : j = anchor
  · subst j
    exact hp.cell0
  · exact hr.markers j hj

end JointThermoComplexity.Complexity.BranchWorkTransfer

#print axioms JointThermoComplexity.Complexity.BranchWorkTransfer.transfer
