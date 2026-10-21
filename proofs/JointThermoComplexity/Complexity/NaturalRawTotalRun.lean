module
public import proofs.JointThermoComplexity.Complexity.NaturalRawControl
public import proofs.JointThermoComplexity.Complexity.NaturalRawCopy

set_option autoImplicit false
@[expose] public section

/-! The existing raw-natural machine decodes every finite raw input in linear
time, including incomplete markers and payloads at EOF. Work is unchanged.
-/

namespace JointThermoComplexity.Complexity.NaturalRawTotalRun
open _root_.Complexity _root_.Complexity.TM NaturalRawMachine
open HeaderAt (Cursor)
variable {w : ℕ}

theorem eof_step (phase : Bool) (c : Cfg w (Option Bool)) (hs : c.state = some phase)
    (before emitted : List Bool) (hc : Cursor before [] emitted c.input c.work c.output) :
    machine.step c = some ⟨none, c.input, c.work, c.output⟩ := by
  have hr : c.input.read = Γ.blank := by
    rw [Tape.read, hc.head, hc.cells, List.append_nil]
    exact Tape.init_ofBool_cells_ge before before.length le_rfl
  cases phase <;> simp only [TM.step, machine, hs, reduceCtorEq, ↓reduceIte, action, hr, allReadBack]
  all_goals
    rw [← hr]
    change some (⟨none, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ :
      Cfg w (Option Bool)) = _
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]

theorem scan_run (input : List Bool) : ∀ (before emitted : List Bool) (c : Cfg w (Option Bool)),
    c.state = some false → Cursor before input emitted c.input c.work c.output →
    ∃ d t, t ≤ input.length + 1 ∧ machine.reachesIn t c d ∧ machine.halted d ∧
      Cursor (before ++ (NaturalRawControl.scan input).taken) (NaturalRawControl.scan input).rest
        (emitted ++ (NaturalRawControl.scan input).bits) d.input d.work d.output ∧ d.work = c.work := by
  induction input using BitCodec.parseBits.induct with
  | case1 =>
    intro before emitted c hs hc
    have he := eof_step false c hs before emitted hc
    exact ⟨⟨none, c.input, c.work, c.output⟩, 1, by simp, .step he .zero, rfl,
      by simpa only [NaturalRawControl.scan, List.append_nil] using hc, rfl⟩
  | case2 rest =>
    intro before emitted c hs hc
    have he := flag_step false c hs (InputCursor.read_bit false hc) (fun j => (hc.works j).1) hc.output_read
    exact ⟨⟨none, c.input.move .right, c.work, c.output⟩, 1, by simp, .step he .zero, rfl,
      by simpa only [NaturalRawControl.scan, List.append_nil] using InputCursor.consume false hc, rfl⟩
  | case3 =>
    intro before emitted c hs hc
    let a : Cfg w (Option Bool) := ⟨some true, c.input.move .right, c.work, c.output⟩
    have he := flag_step true c hs (InputCursor.read_bit true hc) (fun j => (hc.works j).1) hc.output_read
    have ha : Cursor (before ++ [true]) [] emitted a.input a.work a.output := InputCursor.consume true hc
    have hf := eof_step true a rfl (before ++ [true]) emitted ha
    exact ⟨⟨none, a.input, a.work, a.output⟩, 2, by simp, .step he (.step hf .zero), rfl,
      by simpa only [NaturalRawControl.scan, List.append_nil] using ha, rfl⟩
  | case4 b rest ih =>
    intro before emitted c hs hc
    let a : Cfg w (Option Bool) := ⟨some true, c.input.move .right, c.work, c.output⟩
    have hflag := flag_step true c hs (InputCursor.read_bit true hc) (fun j => (hc.works j).1) hc.output_read
    have ha : Cursor (before ++ [true]) (b :: rest) emitted a.input a.work a.output := InputCursor.consume true hc
    let e : Cfg w (Option Bool) :=
      ⟨some false, a.input.move .right, a.work, a.output.writeAndMove (Γ.ofBool b) .right⟩
    have hbit := payload_step b a rfl (InputCursor.read_bit b ha) (fun j => (ha.works j).1)
    have hb := InputCursor.consume b ha
    have he : Cursor ((before ++ [true]) ++ [b]) rest (emitted ++ [b]) e.input e.work e.output :=
      ⟨hb.cells, hb.head, hb.works, Tape.hasBinaryPrefix_write_bit b ha.tapePrefix,
        Tape.hasBinaryPrefix_write_bit_cell0 b ha.tapePrefix ha.zero⟩
    obtain ⟨d, t, ht, hd, hh, hcur, hw⟩ := ih ((before ++ [true]) ++ [b]) (emitted ++ [b]) e rfl he
    refine ⟨d, t + 2, by simp only [List.length_cons]; omega, ?_, hh, ?_, hw⟩
    · simpa only [Nat.add_assoc] using TM.reachesIn.step hflag (TM.reachesIn.step hbit hd)
    · simpa only [NaturalRawControl.scan, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using hcur

theorem hoareTime (input before emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ R work)
      (fun inp work out => Cursor (before ++ (NaturalRawControl.scan input).taken) (NaturalRawControl.scan input).rest
        (emitted ++ (NaturalRawControl.scan input).bits) inp work out ∧ R work) (input.length + 1) := by
  rintro inp work out ⟨hc, hr⟩
  obtain ⟨d, t, ht, hd, hh, hcur, hw⟩ := scan_run input before emitted ⟨some false, inp, work, out⟩ rfl hc
  exact ⟨d, t, ht, hd, hh, hcur, by simpa only [hw] using hr⟩

theorem natural_hoareTime (value : ℕ) (before suffix emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ suffix) emitted inp work out ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) suffix (emitted ++ value.bits) inp work out ∧ R work)
      ((BitCodec.naturalCode value ++ suffix).length + 1) := by
  simpa only [NaturalRawControl.natural] using hoareTime (BitCodec.naturalCode value ++ suffix) before emitted R

end JointThermoComplexity.Complexity.NaturalRawTotalRun

#print axioms JointThermoComplexity.Complexity.NaturalRawTotalRun.scan_run
#print axioms JointThermoComplexity.Complexity.NaturalRawTotalRun.hoareTime
#print axioms JointThermoComplexity.Complexity.NaturalRawTotalRun.natural_hoareTime
