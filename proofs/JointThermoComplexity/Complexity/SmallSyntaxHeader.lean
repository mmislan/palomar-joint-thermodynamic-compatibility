module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxCounter

set_option autoImplicit false
@[expose] public section

/-! Copy the binder once, then clear its counter for the formula/term streaming mode. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxHeader
open _root_.Complexity _root_.Complexity.TM SmallSyntaxRegisters
open HeaderAt (Cursor)

def permutation : Fin 6 ≃ Fin 6 := Equiv.swap 4 pending

theorem counter_eq : HeaderAt.counter permutation = pending := by decide
theorem flag_eq : HeaderAt.flag permutation = flag := by decide

def machine : TM 6 := HeaderAt.machine permutation

def after (s : SmallSyntaxControl.State) : SmallSyntaxControl.State :=
  ⟨s.before ++ HeaderControl.copied s.input, HeaderControl.suffix s.input,
    s.emitted ++ HeaderControl.copied s.input, HeaderControl.count s.input⟩

theorem hoareTime (s : SmallSyntaxControl.State) (hp : s.pending = 0)
    (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    machine.HoareTime (Inv R s) (Inv R (after s)) (2 * HeaderControl.count s.input + 5) := by
  rintro inp work out ⟨hc, hr⟩
  let C : (Fin 6 → Tape) → Prop := fun work' => ∀ j, j ≠ pending → j ≠ flag → work' j = work j
  have hC : ∀ work' work'', (∀ j, j ≠ HeaderAt.counter permutation → j ≠ HeaderAt.flag permutation →
      work'' j = work' j) → C work' → C work'' := by
    intro work' work'' he hprev j hj hf
    exact (he j (by simpa only [counter_eq] using hj) (by simpa only [flag_eq] using hf)).trans (hprev j hj hf)
  have hreg : IsReg 0 (work (HeaderAt.counter permutation)) := by simpa only [counter_eq, hp] using hr.counter
  have hflag : (work (HeaderAt.flag permutation)).head = 1 := by simpa only [flag_eq] using hr.flagHead
  obtain ⟨d, t, ht, hd, hh, hc', hp', hf', _hval, hother⟩ :=
    HeaderAt.hoareTime permutation s.before s.input s.emitted C hC inp work out
      ⟨hc, hreg, hflag, fun _ _ _ => rfl⟩
  have hp'' : IsReg (HeaderControl.count s.input) (d.work pending) := by simpa only [counter_eq] using hp'
  have hf'' : (d.work flag).head = 1 := by simpa only [flag_eq] using hf'
  have hm := VirtualCursor.markers_reaches _ hd (VirtualCursor.input_safe hc)
    (fun j => ⟨hr.markers j, (hr.safe j).2⟩) (VirtualCursor.output_safe hc)
  have hs' : ∀ j, Parked (d.work j) := by
    intro j
    by_cases hj : j = pending
    · subst j; exact hp''.parked
    · by_cases hjf : j = flag
      · subst j
        exact ⟨by rw [hf''], (hm.2.1 flag).2⟩
      · rw [hother j hj hjf]
        exact hr.safe j
  have htags : ∀ i, (d.work (tags i)).head = 1 := by
    intro i
    rw [hother (tags i) (tags_pending i) (tags_flag i)]
    exact hr.tagHeads i
  have hr' := SmallSyntaxRegisters.reframe s.pending (HeaderControl.count s.input) R hR work d.work hr
    (hother fuel (by decide) (by decide)) hs' (fun j => (hm.2.1 j).1) hp'' htags hf''
  exact ⟨d, t, ht, hd, hh, hc', hr'⟩

def setupMachine : TM 6 := seqTM machine (clearWorkTM pending)
def setupState (s : SmallSyntaxControl.State) : SmallSyntaxControl.State := {after s with pending := 0}

theorem setup_hoareTime (s : SmallSyntaxControl.State) (hp : s.pending = 0)
    (R : (Fin 6 → Tape) → Prop) (hR : Stable R) :
    setupMachine.HoareTime (Inv R s) (Inv R (setupState s)) (4 * HeaderControl.count s.input + 11) := by
  have hh := hoareTime s hp R hR
  have hc := SmallSyntaxCounter.clear_hoareTime (HeaderControl.count s.input)
    (after s).before (after s).input (after s).emitted R hR
  have h := seqTM_hoareTime machine (clearWorkTM pending) hh (by
    rintro inp work out ⟨hcur, hr⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨hcur, hr⟩) hc
  exact h.mono_bound (by omega)

end JointThermoComplexity.Complexity.SmallSyntaxHeader

#print axioms JointThermoComplexity.Complexity.SmallSyntaxHeader.hoareTime
#print axioms JointThermoComplexity.Complexity.SmallSyntaxHeader.setup_hoareTime
