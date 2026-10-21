module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxCounter
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxTagRead

set_option autoImplicit false
@[expose] public section

/-! Raw natural copy and signed small-integer expansion preserve the actual syntax-stream registers. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxFields
open _root_.Complexity _root_.Complexity.TM SmallSyntaxRegisters
open HeaderAt (Cursor)

def naturalState (s : SmallSyntaxControl.State) : SmallSyntaxControl.State :=
  ⟨s.before ++ PayloadControl.copied .empty s.input, NumericCursor.naturalRest s.input,
    s.emitted ++ PayloadControl.copied .empty s.input, s.pending⟩

def integerState (s : SmallSyntaxControl.State) : SmallSyntaxControl.State :=
  ⟨s.before ++ SmallIntegerStream.taken s.input, SmallIntegerStream.rest s.input,
    s.emitted ++ SmallIntegerStream.output s.input, s.pending⟩

theorem natural_hoareTime (R : (Fin 6 → Tape) → Prop) (hR : Stable R) (s : SmallSyntaxControl.State) :
    (NaturalMachine.machine false 5).HoareTime (Inv R s) (Inv R (naturalState s)) (s.input.length + 2) := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin 6 → Tape) → Prop := fun work' => ∀ j, j ≠ flag → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ flag → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hj
    exact (he j hj).trans (hp j hj)
  obtain ⟨c, t, ht, hd, hh, hc', hfh, _hfv, hother⟩ :=
    NaturalField.scan_hoareTime false s.before s.input s.emitted C hC
      inp work out ⟨hc, hr.flagHead, fun _ _ => rfl⟩
  change (c.work flag).head = 1 at hfh
  have hs' : ∀ j, Parked (c.work j) := by
    intro j
    by_cases hj : j = flag
    · subst j
      exact ⟨by rw [hfh], TapeSafety.work_reaches flag hd (hr.safe _).2⟩
    · rw [hother j hj]
      exact hr.safe j
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hp : IsReg s.pending (c.work pending) := by simpa only [hother pending (by decide)] using hr.counter
  have htags : ∀ i, (c.work (tags i)).head = 1 :=
    fun i => by simpa only [hother (tags i) (tags_flag i)] using hr.tagHeads i
  have hr' := reframe s.pending s.pending R hR work c.work hr (hother fuel (by decide)) hs'
    (fun j => (hm.2.1 j).1) hp htags hfh
  exact ⟨c, t, ht, hd, hh, hc', hr'⟩

theorem integer_hoareTime (R : (Fin 6 → Tape) → Prop) (hR : Stable R) (s : SmallSyntaxControl.State) :
    (SmallIntegerStreamRun.machine (tags 0) flag).HoareTime (Inv R s) (Inv R (integerState s)) (12 * s.input.length + 13) := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin 6 → Tape) → Prop := fun work' => ∀ j, j ≠ tags 0 → j ≠ flag → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ tags 0 → j ≠ flag → work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hp j hjd hjf
    exact (he j hjd hjf).trans (hp j hjd hjf)
  obtain ⟨c, t, ht, hd, hh, hc', hs', hdh, hfh, hother⟩ :=
    SmallIntegerStreamRun.hoareTime (tags 0) flag (tags_flag 0) s.before s.input s.emitted C hC
      inp work out ⟨hc, hr.safe, hr.tagHeads 0, hr.flagHead, fun _ _ _ => rfl⟩
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hp : IsReg s.pending (c.work pending) := by simpa only [hother pending (by decide) (by decide)] using hr.counter
  have htags : ∀ i, (c.work (tags i)).head = 1 := by
    intro i
    by_cases hi : i = 0
    · subst i
      exact hdh
    · have hne : tags i ≠ tags 0 := fun he => hi (tags_injective he)
      simpa only [hother (tags i) hne (tags_flag i)] using hr.tagHeads i
  have hr' := reframe s.pending s.pending R hR work c.work hr (hother fuel (by decide) (by decide)) hs'
    (fun j => (hm.2.1 j).1) hp htags hfh
  exact ⟨c, t, ht, hd, hh, hc', hr'⟩

end JointThermoComplexity.Complexity.SmallSyntaxFields

#print axioms JointThermoComplexity.Complexity.SmallSyntaxFields.natural_hoareTime
#print axioms JointThermoComplexity.Complexity.SmallSyntaxFields.integer_hoareTime
