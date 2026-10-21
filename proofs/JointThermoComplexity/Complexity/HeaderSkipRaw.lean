module
public import proofs.JointThermoComplexity.Complexity.HeaderSkip
public import proofs.JointThermoComplexity.Complexity.HeaderControl
public import proofs.JointThermoComplexity.Complexity.SourceBitRead

set_option autoImplicit false
@[expose] public section

/-! The existing read-only header machine terminates on every raw word. -/

namespace JointThermoComplexity.Complexity.HeaderSkipRaw
open _root_.Complexity _root_.Complexity.TM
open HeaderAt (Cursor)
open HeaderSkip (machine)
variable {w : ℕ}

theorem blank_step (c : Cfg w (machine (w := w)).Q)
    (hs : c.state = some false) (hr : c.input.read = Γ.blank)
    (hi : c.input.read ≠ Γ.start) (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    machine.step c = some ⟨none, c.input, c.work, c.output⟩ := by
  have hδ : machine.δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      allReadBack none c.input.read (fun j => (c.work j).read) c.output.read := by
    simp [machine, hs, hr]
  rw [TM.step, ite_eq_right (by simp [machine, hs]), hδ]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · exact transitionInput_eq_self hi
  · exact funext (fun j => transitionTape_eq_self (hw j))
  · exact transitionTape_eq_self ho

theorem scan (input : List Bool) : ∀ (before emitted : List Bool) (c : Cfg w (machine (w := w)).Q),
    c.state = some false → Cursor before input emitted c.input c.work c.output →
    ∃ e t, t ≤ HeaderControl.count input + 1 ∧ machine.reachesIn t c e ∧ machine.halted e ∧
      Cursor (before ++ HeaderControl.copied input) (HeaderControl.suffix input) emitted e.input e.work e.output ∧ e.work = c.work := by
  induction input with
  | nil =>
    intro before emitted c hs hc
    let e : Cfg w (machine (w := w)).Q := ⟨none, c.input, c.work, c.output⟩
    have hr : c.input.read = Γ.blank := SourceBitRead.read_symbol hc
    have hstep : machine.step c = some e := blank_step c hs hr hc.input_read (fun j => (hc.works j).1) hc.output_read
    exact ⟨e, 1, le_rfl, .step hstep .zero, rfl, by simpa only [HeaderControl.copied, HeaderControl.suffix, List.append_nil] using hc, rfl⟩
  | cons bit rest ih =>
    intro before emitted c hs hc
    cases bit with
    | false =>
      let e : Cfg w (machine (w := w)).Q := ⟨none, c.input.move .right, c.work, c.output⟩
      have hstep : machine.step c = some e := HeaderSkip.bit_step false c hs (InputCursor.read_bit false hc)
        (fun j => (hc.works j).1) hc.output_read
      exact ⟨e, 1, le_rfl, .step hstep .zero, rfl, InputCursor.consume false hc, rfl⟩
    | true =>
      let d : Cfg w (machine (w := w)).Q := ⟨some false, c.input.move .right, c.work, c.output⟩
      have hstep : machine.step c = some d := HeaderSkip.bit_step true c hs (InputCursor.read_bit true hc)
        (fun j => (hc.works j).1) hc.output_read
      obtain ⟨e, t, ht, hr, hh, hcur, hw⟩ := ih (before ++ [true]) emitted d rfl (InputCursor.consume true hc)
      refine ⟨e, t + 1, by change t + 1 ≤ HeaderControl.count rest + 1 + 1; omega, .step hstep hr, hh, ?_, hw⟩
      simpa only [HeaderControl.copied, HeaderControl.suffix, List.append_assoc, List.cons_append, List.nil_append] using hcur

theorem hoareTime (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor (before ++ HeaderControl.copied input) (HeaderControl.suffix input) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ R work) (HeaderControl.count input + 1) := by
  rintro inp work out ⟨hc, hs, hr⟩
  obtain ⟨e, t, ht, hreach, hhalt, hcur, hw⟩ := scan input before emitted ⟨some false, inp, work, out⟩ rfl hc
  exact ⟨e, t, ht, hreach, hhalt, hcur, by simpa only [hw] using hs, by simpa only [hw] using hr⟩

end JointThermoComplexity.Complexity.HeaderSkipRaw

#print axioms JointThermoComplexity.Complexity.HeaderSkipRaw.hoareTime
