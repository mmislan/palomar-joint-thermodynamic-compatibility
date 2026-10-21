module
public import proofs.JointThermoComplexity.Complexity.NaturalSkip
public import proofs.JointThermoComplexity.Complexity.NumericCursor

set_option autoImplicit false
@[expose] public section

/-! Total read-only natural-field traversal, including malformed and truncated raw words. -/

namespace JointThermoComplexity.Complexity.NaturalSkipRaw
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def phase : PayloadControl.ReadState → Bool
  | .payload => true
  | _ => false

theorem next_phase (p : PayloadControl.ReadState) (bit : Bool) :
    (PayloadControl.next p bit).map phase = NaturalSkip.next (phase p) bit := by
  cases p <;> cases bit <;> rfl

theorem empty_step (p : PayloadControl.ReadState) (c : Cfg w (NaturalSkip.machine (w := w)).Q)
    (hs : c.state = some (phase p)) (hi : c.input.read = Γ.blank)
    (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    NaturalSkip.machine.step c = some ⟨none, c.input, c.work, c.output⟩ := by
  have hd : NaturalSkip.machine.δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      allReadBack none c.input.read (fun j => (c.work j).read) c.output.read := by
    simp [NaturalSkip.machine, hs, hi]
  rw [TM.step, ite_eq_right (by simp [NaturalSkip.machine, hs]), hd]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · exact transitionInput_eq_self (by simp [hi])
  · exact funext (fun j => transitionTape_eq_self (hw j))
  · exact transitionTape_eq_self ho

theorem scan (input : List Bool) : ∀ (p : PayloadControl.ReadState) (before emitted : List Bool)
    (c : Cfg w (NaturalSkip.machine (w := w)).Q), c.state = some (phase p) →
    Cursor before input emitted c.input c.work c.output →
    ∃ d t, t ≤ input.length + 1 ∧ NaturalSkip.machine.reachesIn t c d ∧ NaturalSkip.machine.halted d ∧
      Cursor (before ++ PayloadControl.copied p input) (NumericCursor.payloadRest p input) emitted d.input d.work d.output ∧
      d.work = c.work ∧ d.output = c.output := by
  induction input with
  | nil =>
    intro p before emitted c hs hc
    have hi : c.input.read = Γ.blank := by
      have hcells : c.input.cells = (Tape.init (before.map Γ.ofBool)).cells := by simpa only [List.append_nil] using hc.cells
      simp [Tape.read, hc.head, hcells, Tape.init_ofBool_cells_ge before before.length le_rfl]
    have hstep := empty_step p c hs hi (fun j => (hc.works j).1) hc.output_read
    refine ⟨⟨none, c.input, c.work, c.output⟩, 1, by simp, .step hstep .zero, rfl, ?_, rfl, rfl⟩
    simpa only [PayloadControl.copied, NumericCursor.payloadRest, List.append_nil] using hc
  | cons bit input ih =>
    intro p before emitted c hs hc
    have hn := next_phase p bit
    cases hp : PayloadControl.next p bit with
    | none =>
      have hnext : NaturalSkip.next (phase p) bit = none := by simpa only [hp, Option.map_none] using hn.symm
      let d : Cfg w (NaturalSkip.machine (w := w)).Q := ⟨none, c.input.move .right, c.work, c.output⟩
      have hstep : NaturalSkip.machine.step c = some d := by
        simpa only [hnext] using NaturalSkip.bit_step (phase p) bit c hs (InputCursor.read_bit bit hc)
          (fun j => (hc.works j).1) hc.output_read
      refine ⟨d, 1, by simp, .step hstep .zero, rfl, ?_, rfl, rfl⟩
      simpa only [PayloadControl.copied, NumericCursor.payloadRest, hp] using InputCursor.consume bit hc
    | some q =>
      have hnext : NaturalSkip.next (phase p) bit = some (phase q) := by simpa only [hp, Option.map_some] using hn.symm
      let c' : Cfg w (NaturalSkip.machine (w := w)).Q := ⟨some (phase q), c.input.move .right, c.work, c.output⟩
      have hstep : NaturalSkip.machine.step c = some c' := by
        simpa only [hnext] using NaturalSkip.bit_step (phase p) bit c hs (InputCursor.read_bit bit hc)
          (fun j => (hc.works j).1) hc.output_read
      obtain ⟨d, t, ht, hd, hh, hc', hw, ho⟩ := ih q (before ++ [bit]) emitted c' rfl (InputCursor.consume bit hc)
      refine ⟨d, t + 1, by simp only [List.length_cons]; omega, .step hstep hd, hh, ?_, hw, ho⟩
      simpa only [PayloadControl.copied, NumericCursor.payloadRest, hp, List.append_assoc, List.singleton_append] using hc'

theorem hoareTime (before input emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (NaturalSkip.machine (w := w)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ R work out)
      (fun inp work out => Cursor (before ++ PayloadControl.copied .empty input) (NumericCursor.naturalRest input)
        emitted inp work out ∧ R work out) (input.length + 1) := by
  rintro inp work out ⟨hc, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hw, ho⟩ := scan input .empty before emitted ⟨some false, inp, work, out⟩ rfl hc
  exact ⟨d, t, ht, hd, hh, hc', by simpa only [hw, ho] using hr⟩

end JointThermoComplexity.Complexity.NaturalSkipRaw

#print axioms JointThermoComplexity.Complexity.NaturalSkipRaw.scan
#print axioms JointThermoComplexity.Complexity.NaturalSkipRaw.hoareTime
