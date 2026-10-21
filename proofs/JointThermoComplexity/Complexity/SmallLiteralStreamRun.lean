module
public import proofs.JointThermoComplexity.Complexity.SmallLiteralStreamMachine

set_option autoImplicit false
@[expose] public section

/-! Exact total payload expansion, preserving every work tape predicate, in linear tape steps. -/

namespace JointThermoComplexity.Complexity.SmallLiteralStreamRun
open _root_.Complexity _root_.Complexity.TM HeaderAt SmallLiteralStream SmallLiteralStreamMachine
variable {w : ℕ}

theorem emit_chunk (b : Bool) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before input emitted inp work out)
    (hs : ∀ j, Parked (work j)) (hr : R work) :
    ∃ inp' work' out' t, t ≤ (chunk b).length ∧
      (machine w).reachesIn t ⟨.chunk b 0, inp, work, out⟩ ⟨.marker, inp', work', out'⟩ ∧
      Cursor before input (emitted ++ chunk b) inp' work' out' ∧ (∀ j, Parked (work' j)) ∧ R work' := by
  obtain ⟨d, t, ht, hd, hh, hc', hs', hr'⟩ := FixedOutput.hoareTime (chunk b) before input emitted R inp work out ⟨hc, hs, hr⟩
  have he := chunk_reaches b hd
  have hstart : chunkCfg b ⟨(emitBitsTM (n := w) (chunk b)).qstart, inp, work, out⟩ = ⟨.chunk b 0, inp, work, out⟩ := by
    cases b <;> rfl
  change d.state = (emitBitsTM (n := w) (chunk b)).qhalt at hh
  have hend : chunkCfg b d = ⟨.marker, d.input, d.work, d.output⟩ := by
    apply Cfg.ext
    · change chunkState b d.state = .marker
      rw [hh]
      simp only [chunkState, emitBitsTM, ↓reduceIte]
    · rfl
    · rfl
    · rfl
  rw [hstart, hend] at he
  exact ⟨d.input, d.work, d.output, t, ht, he, hc', hs', hr'⟩

theorem emit_base (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before input emitted inp work out)
    (hs : ∀ j, Parked (work j)) (hr : R work) :
    ∃ inp' work' out' t, t ≤ 5 ∧ (machine w).reachesIn t ⟨.base 0, inp, work, out⟩ ⟨.done, inp', work', out'⟩ ∧
      Cursor before input (emitted ++ base) inp' work' out' ∧ (∀ j, Parked (work' j)) ∧ R work' := by
  obtain ⟨d, t, ht, hd, hh, hc', hs', hr'⟩ := FixedOutput.hoareTime base before input emitted R inp work out ⟨hc, hs, hr⟩
  have he := base_reaches hd
  have hstart : baseCfg ⟨(emitBitsTM (n := w) base).qstart, inp, work, out⟩ = ⟨.base 0, inp, work, out⟩ := rfl
  change d.state = (emitBitsTM (n := w) base).qhalt at hh
  have hend : baseCfg d = ⟨.done, d.input, d.work, d.output⟩ := by
    apply Cfg.ext
    · change baseState d.state = .done
      rw [hh]
      rfl
    · rfl
    · rfl
    · rfl
  rw [hstart, hend] at he
  exact ⟨d.input, d.work, d.output, t, ht, he, hc', hs', hr'⟩

theorem read_step (q q' : State) (b : Bool) (before tail emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before (b :: tail) emitted inp work out)
    (hq : q ≠ .done)
    (ha : action q (Γ.ofBool b) (fun j => (work j).read) out.read =
      advance q' (Γ.ofBool b) (fun j => (work j).read) out.read) :
    (machine w).step ⟨q, inp, work, out⟩ = some ⟨q', inp.move .right, work, out⟩ := by
  have hδ : (machine w).δ q inp.read (fun j => (work j).read) out.read =
      advance q' inp.read (fun j => (work j).read) out.read := by
    rw [InputCursor.read_bit b hc]
    exact ha
  change action q inp.read (fun j => (work j).read) out.read = _ at hδ
  simp only [TM.step, SmallLiteralStreamMachine.machine, hq, ↓reduceIte]
  rw [hδ]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · exact funext (fun j => transitionTape_eq_self (hc.works j).1)
  · exact transitionTape_eq_self hc.output_read

theorem marker_step (b : Bool) (before tail emitted : List Bool) (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before (b :: tail) emitted inp work out) :
    (machine w).step ⟨.marker, inp, work, out⟩ = some ⟨(if b then .bit else .base 0), inp.move .right, work, out⟩ :=
  read_step .marker _ b before tail emitted inp work out hc (by decide) (by cases b <;> rfl)

theorem bit_step (b : Bool) (before tail emitted : List Bool) (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before (b :: tail) emitted inp work out) :
    (machine w).step ⟨.bit, inp, work, out⟩ = some ⟨.chunk b 0, inp.move .right, work, out⟩ :=
  read_step .bit _ b before tail emitted inp work out hc (by decide) (by cases b <;> rfl)

theorem eof_step (q : State) (hq : q = .marker ∨ q = .bit) (before emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before [] emitted inp work out) :
    (machine w).step ⟨q, inp, work, out⟩ = some ⟨.base 0, inp, work, out⟩ := by
  have hn : q ≠ .done := by rcases hq with rfl | rfl <;> decide
  have hr : inp.read = Γ.blank := by
    rw [Tape.read, hc.head, hc.cells, List.append_nil]
    exact Tape.init_ofBool_cells_ge before before.length le_rfl
  have ha : (machine w).δ q inp.read (fun j => (work j).read) out.read =
      allReadBack (.base 0) inp.read (fun j => (work j).read) out.read := by
    rw [hr]
    rcases hq with rfl | rfl <;> rfl
  change action q inp.read (fun j => (work j).read) out.read = _ at ha
  simp only [TM.step, SmallLiteralStreamMachine.machine, hn, ↓reduceIte]
  rw [ha]
  change some (⟨.base 0, transitionInput inp, (fun j => transitionTape (work j)), transitionTape out⟩ : Cfg w (machine w).Q) = _
  obtain ⟨hi, hw, ho⟩ := hc.phase
  rw [hi, hw, ho]
  rfl

theorem run (input before emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before input emitted inp work out)
    (hs : ∀ j, Parked (work j)) (hr : R work) :
    ∃ inp' work' out' t, t ≤ 12 * input.length + 6 ∧
      (machine w).reachesIn t ⟨.marker, inp, work, out⟩ ⟨.done, inp', work', out'⟩ ∧
      Cursor (before ++ (scan input).taken) (scan input).rest (emitted ++ output (scan input).bits) inp' work' out' ∧
        (∀ j, Parked (work' j)) ∧ R work' := by
  induction input using BitCodec.parseBits.induct generalizing before emitted inp work out with
  | case1 =>
    have he := eof_step .marker (Or.inl rfl) before emitted inp work out hc
    obtain ⟨inp', work', out', t, ht, hd, hc', hs', hr'⟩ := emit_base before [] emitted R inp work out hc hs hr
    exact ⟨inp', work', out', t + 1, by simp only [List.length_nil]; omega, .step he hd,
      by simpa only [scan, output_nil, List.append_nil] using hc', hs', hr'⟩
  | case2 rest =>
    have he := marker_step false before rest emitted inp work out hc
    have hcur := InputCursor.consume false hc
    obtain ⟨inp', work', out', t, ht, hd, hc', hs', hr'⟩ :=
      emit_base (before ++ [false]) rest emitted R (inp.move .right) work out hcur hs hr
    exact ⟨inp', work', out', t + 1, by simp only [List.length_cons]; omega, .step he hd,
      by simpa only [scan, output_nil] using hc', hs', hr'⟩
  | case3 =>
    have he := marker_step true before [] emitted inp work out hc
    have hcur := InputCursor.consume true hc
    have hf := eof_step .bit (Or.inr rfl) (before ++ [true]) emitted (inp.move .right) work out hcur
    obtain ⟨inp', work', out', t, ht, hd, hc', hs', hr'⟩ :=
      emit_base (before ++ [true]) [] emitted R (inp.move .right) work out hcur hs hr
    exact ⟨inp', work', out', t + 2, by simp only [List.length_cons, List.length_nil]; omega,
      by simpa only [Nat.add_assoc] using TM.reachesIn.step he (TM.reachesIn.step hf hd),
      by simpa only [scan, output_nil] using hc', hs', hr'⟩
  | case4 b rest ih =>
    have he := marker_step true before (b :: rest) emitted inp work out hc
    have hcur := InputCursor.consume true hc
    have hf := bit_step b (before ++ [true]) rest emitted (inp.move .right) work out hcur
    have hcur' := InputCursor.consume b hcur
    obtain ⟨inp1, work1, out1, tc, htc, hdc, hcc, hsc, hrc⟩ :=
      emit_chunk b ((before ++ [true]) ++ [b]) rest emitted R ((inp.move .right).move .right) work out hcur' hs hr
    obtain ⟨inp', work', out', t, ht, hd, hc', hs', hr'⟩ := ih _ _ _ _ _ hcc hsc hrc
    have hread : (machine w).reachesIn (tc + 2) ⟨.marker, inp, work, out⟩ ⟨.marker, inp1, work1, out1⟩ := by
      simpa only [Nat.add_assoc] using TM.reachesIn.step he (TM.reachesIn.step hf hdc)
    have hb := (chunk_bound b).2
    refine ⟨inp', work', out', tc + 2 + t, by simp only [List.length_cons]; omega,
      reachesIn_trans _ hread hd, ?_, hs', hr'⟩
    simpa only [scan, output_cons, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using hc'

theorem hoareTime (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine w).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor (before ++ (scan input).taken) (scan input).rest
        (emitted ++ output (scan input).bits) inp work out ∧ (∀ j, Parked (work j)) ∧ R work) (12 * input.length + 6) := by
  rintro inp work out ⟨hc, hs, hr⟩
  obtain ⟨inp', work', out', t, ht, hd, hc', hs', hr'⟩ := run input before emitted R inp work out hc hs hr
  exact ⟨⟨.done, inp', work', out'⟩, t, ht, hd, rfl, hc', hs', hr'⟩

theorem encoded_hoareTime (n : ℕ) (bits before suffix emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine w).HoareTime
      (fun inp work out => Cursor before (BitCodec.encodeBits bits ++ suffix) emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.encodeBits bits) suffix
        (emitted ++ (SourceSmallLiterals.fromBits bits : RealSyntax.Term n).code) inp work out ∧
          (∀ j, Parked (work j)) ∧ R work) (12 * (BitCodec.encodeBits bits ++ suffix).length + 6) := by
  simpa only [scan_encoded, fromBits_code] using hoareTime before (BitCodec.encodeBits bits ++ suffix) emitted R

end JointThermoComplexity.Complexity.SmallLiteralStreamRun

#print axioms JointThermoComplexity.Complexity.SmallLiteralStreamRun.hoareTime
#print axioms JointThermoComplexity.Complexity.SmallLiteralStreamRun.encoded_hoareTime
