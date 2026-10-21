module
public import proofs.JointThermoComplexity.Complexity.TermSpanCounter

set_option autoImplicit false
@[expose] public section

/-! Fresh-presence tag reading preserves both measured counters and every outside tape. -/

namespace JointThermoComplexity.Complexity.TermSpanTagRead
open _root_.Complexity _root_.Complexity.TM TermSpanRegisters
open HeaderAt (Cursor)
variable {n : ℕ}

def afterTag (s : TermSpanControl.State) : TermSpanControl.State :=
  ⟨s.before ++ s.input.take 3, s.input.drop 3, s.pending, s.nodes⟩

def readMachine (n : ℕ) : TM (n + 7) := SourceTagFlags.machine (tags n) (flag n)
def machine (n : ℕ) : TM (n + 7) := seqTM (SourceTermToken.setStatus (flag n) false) (readMachine n)

theorem read_hoareTime (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R) (s : TermSpanControl.State) :
    (readMachine n).HoareTime
      (fun inp work out => Inv emitted R s inp work out ∧ (work (flag n)).read = Γ.zero)
      (fun inp work out => Inv emitted R (afterTag s) inp work out ∧
        (work (flag n)).read = Γ.ofBool (SourceTags.accepted s.input) ∧
        SourceTagDispatch.Reads (List.ofFn (tags n)) (SourceTermToken.tagBits s.input) work) 6 := by
  rintro inp work out ⟨⟨hc, hr⟩, hf⟩
  let C : (Fin (n + 7) → Tape) → Prop := fun work' => ∀ j, (∀ i, j ≠ tags n i) → j ≠ flag n → work' j = work j
  have hC : ∀ work' work'', (∀ j, (∀ i, j ≠ tags n i) → j ≠ flag n → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj ht
    exact (he j hj ht).trans (hp j hj ht)
  obtain ⟨d, t, ht, hd, hh, hc', hs', htags, hflag, hv, hdata, hother⟩ :=
    SourceTagFlags.tag_hoareTime (tags n) (tags_injective n) (flag n) (tags_flag n) false s.before s.input emitted C hC
      inp work out ⟨hc, hr.safe, hr.tagHeads, hr.flagHead, hf, fun _ _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hp : IsReg s.pending (d.work (pending n)) := by
    rw [hother _ (fun i => (tags_pending n i).symm) (pending_flag n)]
    exact hr.counter
  have hn : IsReg s.nodes (d.work (nodeCounter n)) := by
    rw [hother _ (fun i => (tags_nodeCounter n i).symm) (nodeCounter_flag n)]
    exact hr.nodeReg
  have hr' := reframe s.pending s.pending s.nodes s.nodes R hR work d.work hr
    (fun j hj => hother j hj.2.2.2 hj.2.2.1) hs' (fun j => (hm.2.1 j).1) hp hn htags hflag
  have hreads : SourceTagDispatch.Reads (List.ofFn (tags n)) (SourceTermToken.tagBits s.input) d.work := by
    change (d.work (tags n 0)).read = Γ.ofBool (SourceBitRead.value s.input) ∧
      (d.work (tags n 1)).read = Γ.ofBool (SourceBitRead.value (s.input.drop 1)) ∧
      (d.work (tags n 2)).read = Γ.ofBool (SourceBitRead.value (s.input.drop 2)) ∧ True
    exact ⟨by simpa only [Fin.val_zero, List.drop_zero] using hdata 0, hdata 1, hdata 2, trivial⟩
  exact ⟨d, t, ht, hd, hh, ⟨hc', hr'⟩, hv, hreads⟩

theorem hoareTime (emitted : List Bool) (R : (Fin (n + 7) → Tape) → Prop) (hR : Stable R) (s : TermSpanControl.State) :
    (machine n).HoareTime (Inv emitted R s)
      (fun inp work out => Inv emitted R (afterTag s) inp work out ∧
        (work (flag n)).read = Γ.ofBool (SourceTags.accepted s.input) ∧
        SourceTagDispatch.Reads (List.ofFn (tags n)) (SourceTermToken.tagBits s.input) work) 8 := by
  have hs := status_hoareTime false emitted R hR s
  have hr := read_hoareTime emitted R hR s
  exact seqTM_hoareTime (SourceTermToken.setStatus (flag n) false) (readMachine n) hs (by
    rintro inp work out ⟨⟨hc, hp⟩, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, hp⟩, hf⟩) hr

end JointThermoComplexity.Complexity.TermSpanTagRead

#print axioms JointThermoComplexity.Complexity.TermSpanTagRead.hoareTime
