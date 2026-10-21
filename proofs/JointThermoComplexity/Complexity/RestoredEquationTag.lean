module
public import proofs.JointThermoComplexity.Complexity.BranchWorkTransfer

set_option autoImplicit false
@[expose] public section

/-! Read fresh tag and presence bits, then restore the exact node cursor before selecting a branch. -/

namespace JointThermoComplexity.Complexity.RestoredEquationTag
open _root_.Complexity _root_.Complexity.TM RelocatedSpanQuery QueryWorkFrame QueryCounterInit LocalBranchState
open HeaderAt (Cursor)

def forward : TM 32 := seqTM (SourceTermToken.setStatus flag false) (SourceTagFlags.machine tags flag)
def machine : TM 32 := InputCheckpoint.around anchor forward

def Reading (input : List Bool) (work : Work) : Prop :=
  (work flag).read = Γ.ofBool (SourceTags.accepted input) ∧
    ∀ i, (work (tags i)).read = Γ.ofBool (SourceBitRead.value (input.drop i.val))

theorem tags_flag (i : Fin 3) : tags i ≠ flag := by
  intro he
  have hv := congrArg Fin.val he
  change i.val + 8 = 14 at hv
  omega

theorem tags_anchor (i : Fin 3) : tags i ≠ anchor := by
  intro he
  have hv := congrArg Fin.val he
  change i.val + 8 = 30 at hv
  omega

theorem reading_anchor (input : List Bool) :
    ∀ work work', (∀ j, j ≠ anchor → work' j = work j) → Reading input work → Reading input work' := by
  rintro work work' he ⟨hf, ht⟩
  exact ⟨by simpa only [he _ (by decide : flag ≠ anchor)] using hf,
    fun i => by simpa only [he _ (tags_anchor i)] using ht i⟩

theorem reads (input : List Bool) (work : Work) (hr : Reading input work) :
    SourceTagDispatch.Reads (List.ofFn tags) (SourceTermToken.tagBits input) work := by
  change (work (tags 0)).read = Γ.ofBool (SourceBitRead.value input) ∧
    (work (tags 1)).read = Γ.ofBool (SourceBitRead.value (input.drop 1)) ∧
      (work (tags 2)).read = Γ.ofBool (SourceBitRead.value (input.drop 2)) ∧ True
  exact ⟨by simpa only [Fin.val_zero, List.drop_zero] using hr.2 0, hr.2 1, hr.2 2, trivial⟩

theorem forward_hoareTime (counts : Counts) (values : Fin 9 → ℕ) (L p : ℕ)
    (before input emitted : List Bool) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    forward.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg p (work anchor) ∧ Ready counts values L R work)
      (fun inp work out => Cursor (before ++ input.take 3) (input.drop 3) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ IsReg p (work anchor) ∧ Ready counts values L R work ∧ Reading input work) 8 := by
  rintro inp work out ⟨hc, hs, hp, hr⟩
  let C : Work → Prop := fun work' => ∀ j, (∀ i, j ≠ tags i) → j ≠ flag → work' j = work j
  let D : Work → Prop := fun work' => (∀ i, (work' (tags i)).head = 1) ∧ C work'
  have hC : ∀ work' work'', (∀ j, (∀ i, j ≠ tags i) → j ≠ flag → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hh j ht hf
    exact (he j ht hf).trans (hh j ht hf)
  have hD : ∀ work' work'', (∀ j, j ≠ flag → work'' j = work' j) → D work' → D work'' := by
    rintro work' work'' he ⟨ht, hh⟩
    exact ⟨fun i => by simpa only [he _ (tags_flag i)] using ht i,
      fun j hj hf => (he j hf).trans (hh j hj hf)⟩
  have hset := SourceTermToken.setStatus_hoareTime flag false before input emitted D hD
  have hread := SourceTagFlags.tag_hoareTime tags (by
    intro i j he
    have hv := congrArg Fin.val he
    apply Fin.ext
    change i.val + 8 = j.val + 8 at hv
    omega) flag tags_flag false before input emitted C hC
  have hseq := seqTM_hoareTime (SourceTermToken.setStatus flag false) (SourceTagFlags.machine tags flag) hset (by
    rintro inp work out ⟨hcur, hw, hf, hread, ht, hh⟩
    obtain ⟨hin, hwork, hout⟩ := hcur.phase
    rw [hin, hwork, hout]
    exact ⟨hcur, hw, ht, hf, hread, hh⟩) hread
  obtain ⟨d, t, ht, hd, hh, hc', hs', htags, hflag, hf, hbits, he⟩ :=
    hseq inp work out ⟨hc, hs, hr.basic.flagHead, hr.basic.tagHeads, fun _ _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨BranchWorkTransfer.full_markers counts values L p R work hr hp j, (hs j).2⟩)
    (VirtualCursor.output_safe hc)
  have hr' := BranchWorkTransfer.transfer counts values L R hR work d.work hr
    (fun j hj => he j hj.1 hj.2.1) htags hflag (fun j _ => (hm.2.1 j).1)
  have ha : ∀ i, anchor ≠ tags i := fun i => (tags_anchor i).symm
  exact ⟨d, t, ht, hd, hh, hc', hs', by simpa only [he anchor ha (by decide : anchor ≠ flag)] using hp,
    hr', hf, hbits⟩

theorem hoareTime (counts : Counts) (values : Fin 9 → ℕ) (L : ℕ)
    (before input emitted : List Bool) (R : Work → Prop) (hR : LocalBranchState.Stable R) :
    machine.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work anchor) ∧ Ready counts values L R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work anchor) ∧ Ready counts values L R work ∧ Reading input work)
      (13 * before.length + input.length + 31) := by
  have hQ : ∀ work work', (∀ j, j ≠ anchor → work' j = work j) →
      (Ready counts values L R work ∧ Reading input work) → (Ready counts values L R work' ∧ Reading input work') := by
    rintro work work' he ⟨hr, ht⟩
    exact ⟨ready_anchor counts values L R hR work work' he hr, reading_anchor input work work' he ht⟩
  have h := InputCheckpointTransition.hoareTime anchor forward before input (before ++ input.take 3) (input.drop 3)
    emitted emitted (by simp only [List.append_assoc, List.take_append_drop])
    (Ready counts values L R) (fun work => Ready counts values L R work ∧ Reading input work)
    (ready_anchor counts values L R hR) hQ 8 (forward_hoareTime counts values L before.length before input emitted R hR)
  apply h.mono_bound
  simp only [List.length_append, List.length_take]
  omega

end JointThermoComplexity.Complexity.RestoredEquationTag

#print axioms JointThermoComplexity.Complexity.RestoredEquationTag.forward_hoareTime
#print axioms JointThermoComplexity.Complexity.RestoredEquationTag.hoareTime
