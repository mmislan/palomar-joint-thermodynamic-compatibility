module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxRegisters

set_option autoImplicit false
@[expose] public section

/-! Read fixed-width tags with a fresh presence flag and exact six-tape streaming frame. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxTagRead
open _root_.Complexity _root_.Complexity.TM SmallSyntaxRegisters
open HeaderAt (Cursor)

def afterTag (s : SmallSyntaxControl.State) : SmallSyntaxControl.State :=
  ⟨s.before ++ s.input.take 3, s.input.drop 3, s.emitted, s.pending⟩

def readMachine : TM 6 := SourceTagFlags.machine tags flag
def machine : TM 6 := seqTM (SourceTermToken.setStatus flag false) readMachine

theorem read_hoareTime (R : (Fin 6 → Tape) → Prop) (hR : Stable R) (s : SmallSyntaxControl.State) :
    readMachine.HoareTime
      (fun inp work out => Inv R s inp work out ∧ (work flag).read = Γ.zero)
      (fun inp work out => Inv R (afterTag s) inp work out ∧ (work flag).read = Γ.ofBool (SourceTags.accepted s.input) ∧
        SourceTagDispatch.Reads (List.ofFn tags) (SourceTermToken.tagBits s.input) work) 6 := by
  rintro inp work out ⟨⟨hc, hr⟩, hf⟩
  let C : (Fin 6 → Tape) → Prop := fun work' => ∀ j, (∀ i, j ≠ tags i) → j ≠ flag → work' j = work j
  have hC : ∀ work' work'', (∀ j, (∀ i, j ≠ tags i) → j ≠ flag → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj ht
    exact (he j hj ht).trans (hp j hj ht)
  obtain ⟨c, t, ht, hd, hh, hc', hs', htags, hflag, hv, hdata, hother⟩ :=
    SourceTagFlags.tag_hoareTime tags tags_injective flag tags_flag false s.before s.input s.emitted C hC
      inp work out ⟨hc, hr.safe, hr.tagHeads, hr.flagHead, hf, fun _ _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hp : IsReg s.pending (c.work pending) := by
    simpa only [hother pending (fun i => (tags_pending i).symm) (by decide)] using hr.counter
  have hr' := reframe s.pending s.pending R hR work c.work hr (hother fuel fuel_tags (by decide)) hs'
    (fun j => (hm.2.1 j).1) hp htags hflag
  have hreads : SourceTagDispatch.Reads (List.ofFn tags) (SourceTermToken.tagBits s.input) c.work := by
    change (c.work (tags 0)).read = Γ.ofBool (SourceBitRead.value s.input) ∧
      (c.work (tags 1)).read = Γ.ofBool (SourceBitRead.value (s.input.drop 1)) ∧
      (c.work (tags 2)).read = Γ.ofBool (SourceBitRead.value (s.input.drop 2)) ∧ True
    exact ⟨by simpa only [Fin.val_zero, List.drop_zero] using hdata 0, hdata 1, hdata 2, trivial⟩
  exact ⟨c, t, ht, hd, hh, ⟨hc', hr'⟩, hv, hreads⟩

theorem hoareTime (R : (Fin 6 → Tape) → Prop) (hR : Stable R) (s : SmallSyntaxControl.State) :
    machine.HoareTime (Inv R s)
      (fun inp work out => Inv R (afterTag s) inp work out ∧ (work flag).read = Γ.ofBool (SourceTags.accepted s.input) ∧
        SourceTagDispatch.Reads (List.ofFn tags) (SourceTermToken.tagBits s.input) work) 8 := by
  have hs := status_hoareTime false R hR s
  have hr := read_hoareTime R hR s
  have h := seqTM_hoareTime (SourceTermToken.setStatus flag false) readMachine hs (by
    rintro inp work out ⟨⟨hc, hp⟩, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, hp⟩, hf⟩) hr
  exact h.mono_bound le_rfl

end JointThermoComplexity.Complexity.SmallSyntaxTagRead

#print axioms JointThermoComplexity.Complexity.SmallSyntaxTagRead.hoareTime
