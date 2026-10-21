module
public import proofs.JointThermoComplexity.Complexity.NaturalRawMachine

set_option autoImplicit false
@[expose] public section

/-! Exact raw-payload decoding of a canonical natural field, with no numeric-value loop. -/

namespace JointThermoComplexity.Complexity.NaturalRawCopy
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt NaturalRawMachine

variable {w : ℕ}

theorem scan (bits : List Bool) : ∀ (before tail emitted : List Bool) (c : Cfg w (Option Bool)),
    c.state = some false → Cursor before (BitCodec.encodeBits bits ++ tail) emitted c.input c.work c.output →
    ∃ d, (machine (w := w)).reachesIn (2 * bits.length + 1) c d ∧ machine.halted d ∧
      Cursor (before ++ BitCodec.encodeBits bits) tail (emitted ++ bits) d.input d.work d.output ∧ d.work = c.work := by
  induction bits with
  | nil =>
    intro before tail emitted c hs hc
    have hc' : Cursor before (false :: tail) emitted c.input c.work c.output := by
      simpa only [BitCodec.encodeBits, List.singleton_append] using hc
    let d : Cfg w (Option Bool) := ⟨none, c.input.move .right, c.work, c.output⟩
    have hstep : machine.step c = some d := flag_step false c hs (InputCursor.read_bit false hc')
      (fun j => (hc'.works j).1) hc'.output_read
    exact ⟨d, .step hstep .zero, rfl,
      by simpa only [BitCodec.encodeBits, List.append_nil] using InputCursor.consume false hc', rfl⟩
  | cons b bits ih =>
    intro before tail emitted c hs hc
    have hc' : Cursor before (true :: b :: (BitCodec.encodeBits bits ++ tail)) emitted c.input c.work c.output := by
      simpa only [BitCodec.encodeBits, List.cons_append] using hc
    let a : Cfg w (Option Bool) := ⟨some true, c.input.move .right, c.work, c.output⟩
    have hflag : machine.step c = some a := flag_step true c hs (InputCursor.read_bit true hc')
      (fun j => (hc'.works j).1) hc'.output_read
    have ha : Cursor (before ++ [true]) (b :: (BitCodec.encodeBits bits ++ tail)) emitted a.input a.work a.output :=
      InputCursor.consume true hc'
    let e : Cfg w (Option Bool) := ⟨some false, a.input.move .right, a.work, a.output.writeAndMove (Γ.ofBool b) .right⟩
    have hbit : machine.step a = some e := payload_step b a rfl (InputCursor.read_bit b ha) (fun j => (ha.works j).1)
    have hb := InputCursor.consume b ha
    have he : Cursor ((before ++ [true]) ++ [b]) (BitCodec.encodeBits bits ++ tail) (emitted ++ [b]) e.input e.work e.output :=
      ⟨hb.cells, hb.head, hb.works, Tape.hasBinaryPrefix_write_bit b ha.tapePrefix,
        Tape.hasBinaryPrefix_write_bit_cell0 b ha.tapePrefix ha.zero⟩
    obtain ⟨d, hd, hh, hcur, hw⟩ := ih ((before ++ [true]) ++ [b]) tail (emitted ++ [b]) e rfl he
    refine ⟨d, ?_, hh, ?_, hw⟩
    · have hsteps := reachesIn.step hflag (reachesIn.step hbit hd)
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hsteps
    · simpa only [BitCodec.encodeBits, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using hcur

theorem hoareTime (bits before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before (BitCodec.encodeBits bits ++ tail) emitted inp work out ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.encodeBits bits) tail (emitted ++ bits) inp work out ∧ R work)
      (2 * bits.length + 1) := by
  rintro inp work out ⟨hc, hr⟩
  obtain ⟨d, hd, hh, hcur, hw⟩ := scan bits before tail emitted ⟨some false, inp, work, out⟩ rfl hc
  exact ⟨d, 2 * bits.length + 1, le_rfl, hd, hh, hcur, by simpa only [hw] using hr⟩

theorem natural_hoareTime (value : ℕ) (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail (emitted ++ value.bits) inp work out ∧ R work)
      (2 * value.bits.length + 1) :=
  hoareTime value.bits before tail emitted R

end JointThermoComplexity.Complexity.NaturalRawCopy

#print axioms JointThermoComplexity.Complexity.NaturalRawCopy.scan
#print axioms JointThermoComplexity.Complexity.NaturalRawCopy.natural_hoareTime
