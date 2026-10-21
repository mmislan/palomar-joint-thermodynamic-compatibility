module
public import proofs.JointThermoComplexity.Complexity.SourceTermControl

set_option autoImplicit false
@[expose] public section

/-! Pending-child arithmetic preserves the source parser's shared state and verdict. -/

namespace JointThermoComplexity.Complexity.SourcePendingFrame
open _root_.Complexity _root_.Complexity.TM HeaderAt SourceIndexField SourceTermToken SourceTermTokenRun
variable {n : ℕ}

structure Separate (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1)) : Prop where
  left : pending ≠ left
  right : pending ≠ right
  flag : pending ≠ NaturalMachine.flagIndex n
  tags : ∀ i, pending ≠ ports i

theorem cast_ne {a b : Fin (n + 1)} (h : a ≠ b) : a.castSucc ≠ b.castSucc := by
  intro he
  apply h
  apply Fin.ext
  exact congrArg (fun i : Fin (n + 2) => i.val) he

theorem buffer_ne (pending : Fin (n + 1)) : NaturalScanBuffer.buffer n ≠ pending.castSucc := by
  intro he
  have hv := congrArg (fun i : Fin (n + 2) => i.val) he
  change n + 1 = pending.val at hv
  have := pending.isLt
  omega

theorem hoareTime (ports : Fin 3 → Fin (n + 1)) (pending left right : Fin (n + 1))
    (sep : Separate ports pending left right) (L arity v : ℕ) (value : Bool)
    (source before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ pending → work' j = work j) → R work → R work') :
    (SourcePendingUpdate.machine (fun i => (ports i).castSucc) pending.castSucc).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work ∧
        IsReg (v + 1) (work pending.castSucc) ∧ TagState ports source (fun j => work j.castSucc) ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool value)
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready L left right arity R work ∧
        IsReg (v + children (classify (tagBits source))) (work pending.castSucc) ∧
        TagState ports source (fun j => work j.castSucc) ∧
        (work (NaturalScanBuffer.flag n)).read = Γ.ofBool value) (2 * v + 18) := by
  rintro inp work out ⟨hc, hr, hp, htags, hf⟩
  let C : (Fin (n + 2) → Tape) → Prop := fun work' => ∀ j, j ≠ pending.castSucc → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ pending.castSucc → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  have h := SourcePendingUpdate.hoareTime (fun i => (ports i).castSucc) pending.castSucc (tagBits source)
    (by simp [tagBits]) v before input emitted C hC
  obtain ⟨d, t, ht, hd, hh, hc', hs', hp', hother⟩ := h inp work out
    ⟨hc, ⟨hr.safe, hp, fun _ _ => rfl⟩,
      SourceTermTagRead.reads_of_values ports source work (fun i => (htags i).2)⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hl := hother left.castSucc (cast_ne sep.left.symm)
  have hright := hother right.castSucc (cast_ne sep.right.symm)
  have hflag := hother (NaturalScanBuffer.flag n) (cast_ne sep.flag.symm)
  have hbuf := hother (NaturalScanBuffer.buffer n) (buffer_ne pending)
  have hr' : Ready L left right arity R d.work :=
    ⟨hs', fun j => (hm.2.1 j).1, by simpa only [hbuf] using hr.encoded,
      by simpa only [hl] using hr.candidate, by simpa only [hright] using hr.arityBits,
      by simpa only [hright] using hr.arityZero, by simpa only [hflag] using hr.flagHead,
      hR _ _ (fun j hj => hother j.castSucc (cast_ne hj)) hr.frame⟩
  have htags' : TagState ports source (fun j => d.work j.castSucc) := by
    intro i
    simpa only [hother (ports i).castSucc (cast_ne (sep.tags i).symm)] using htags i
  exact ⟨d, t, ht, hd, hh, hc', hr', hp', htags', by simpa only [hflag] using hf⟩

end JointThermoComplexity.Complexity.SourcePendingFrame

#print axioms JointThermoComplexity.Complexity.SourcePendingFrame.hoareTime
