module
public import proofs.JointThermoComplexity.Complexity.BranchWorkTransfer

set_option autoImplicit false
@[expose] public section

/-! Leaf emission uses the same physical work contract as all nonleaf/formula branches. -/

namespace JointThermoComplexity.Complexity.BranchLeafEmission
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryWorkFrame QueryCounterInit LocalBranchState
open HeaderAt (Cursor)

theorem hoareTime (isVar : Bool) (counts : Counts) (values : Fin 9 → ℕ) (L B : ℕ)
    (hv : values 0 ≤ B) (before input emitted : List Bool) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    (LeafLocalEquation.machine isVar).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work anchor) ∧ Ready counts values L R work)
      (fun inp work out => Cursor before input (emitted ++ LeafLocalEquation.output isVar (values 0) input) inp work out ∧
        (∀ j, Parked (work j)) ∧ IsReg 0 (work anchor) ∧ Ready counts values L R work)
      (ReusableIndexEmitter.timeBound B + 2 * input.length + 13 * before.length + 70) := by
  rintro inp work out ⟨hc, hs, hp, hr⟩
  let C : Work → Prop := fun work' => ∀ j, j ≠ flag → j ≠ anchor → work' j = work j
  have hC : LeafLocalEquation.Stable C := by
    intro work' work'' he hh j hf ha
    exact (he j hf ha).trans (hh j hf ha)
  obtain ⟨d, t, ht, hd, hh, hc', hs', hp', hl⟩ :=
    LeafLocalEquation.hoareTime isVar (values 0) B hv before input emitted C hC inp work out
      ⟨hc, hs, hp, hr.addresses 0, hr.basic.scratchReg, hr.basic.flagHead, hr.markers, fun _ _ _ => rfl⟩
  have he := hl.frame
  have htags : ∀ i, (d.work (tags i)).head = 1 := by
    intro i
    have hf : tags i ≠ flag := by
      intro heq
      have hn := congrArg Fin.val heq
      change i.val + 8 = 14 at hn
      omega
    have ha : tags i ≠ anchor := by
      intro heq
      have hn := congrArg Fin.val heq
      change i.val + 8 = 30 at hn
      omega
    simpa only [he _ hf ha] using hr.basic.tagHeads i
  have hr' := BranchWorkTransfer.transfer counts values L R hR work d.work hr
    (fun j hj => he j hj.2.1 hj.2.2) htags hl.flagHead hl.markers
  exact ⟨d, t, ht, hd, hh, hc', hs', hp', hr'⟩

end JointThermoComplexity.Complexity.BranchLeafEmission

#print axioms JointThermoComplexity.Complexity.BranchLeafEmission.hoareTime
