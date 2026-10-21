module
public import proofs.JointThermoComplexity.Complexity.EquationCoefficientMachine
public import proofs.JointThermoComplexity.Complexity.EquationCoefficientControl

set_option autoImplicit false
@[expose] public section

/-! Adapted from the checked small-coefficient run proof pattern.

 Linear signed-field extraction, with exact suffixes and arbitrary parked work frames. -/

namespace JointThermoComplexity.Complexity.EquationCoefficientRun
open _root_.Complexity _root_.Complexity.TM HeaderAt EquationCoefficientControl EquationCoefficientMachine
variable {w : ℕ}

theorem emit_word (negate negative : Bool) (m : Magnitude) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before input emitted inp work out) (hs : ∀ j, Parked (work j)) (hr : R work) :
    ∃ inp' work' out' t, t ≤ 8 ∧
      (machine negate w).reachesIn t ⟨.emit negative m 0, inp, work, out⟩ ⟨.done, inp', work', out'⟩ ∧
      Cursor before input (emitted ++ word negate negative m) inp' work' out' ∧
        (∀ j, Parked (work' j)) ∧ R work' := by
  obtain ⟨d, t, ht, hd, hh, hc', hs', hr'⟩ :=
    FixedOutput.hoareTime (word negate negative m) before input emitted R inp work out ⟨hc, hs, hr⟩
  have he := emit_reaches negate negative m hd
  have hstart : emitCfg negate negative m
      ⟨(emitBitsTM (n := w) (word negate negative m)).qstart, inp, work, out⟩ =
        ⟨.emit negative m 0, inp, work, out⟩ := by
    cases negate <;> cases negative <;> cases m <;> rfl
  change d.state = (emitBitsTM (n := w) (word negate negative m)).qhalt at hh
  have hend : emitCfg negate negative m d = ⟨.done, d.input, d.work, d.output⟩ := by
    apply Cfg.ext
    · change emitState negate negative m d.state = .done
      rw [hh]
      simp only [emitState, emitBitsTM, ↓reduceIte]
    · rfl
    · rfl
    · rfl
  rw [hstart, hend] at he
  exact ⟨d.input, d.work, d.output, t, ht.trans (word_bound negate negative m), he, hc', hs', hr'⟩

theorem read_step (negate : Bool) (q q' : State) (b : Bool) (before tail emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before (b :: tail) emitted inp work out)
    (hq : q ≠ .done)
    (ha : action negate q (Γ.ofBool b) (fun j => (work j).read) out.read =
      advance q' (Γ.ofBool b) (fun j => (work j).read) out.read) :
    (machine negate w).step ⟨q, inp, work, out⟩ = some ⟨q', inp.move .right, work, out⟩ := by
  have hδ : (machine negate w).δ q inp.read (fun j => (work j).read) out.read =
      advance q' inp.read (fun j => (work j).read) out.read := by
    rw [InputCursor.read_bit b hc]
    exact ha
  change action negate q inp.read (fun j => (work j).read) out.read = _ at hδ
  simp only [TM.step, EquationCoefficientMachine.machine, hq, ↓reduceIte]
  rw [hδ]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · exact funext (fun j => transitionTape_eq_self (hc.works j).1)
  · exact transitionTape_eq_self hc.output_read

theorem sign_step (negate b : Bool) (before tail emitted : List Bool) (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before (b :: tail) emitted inp work out) :
    (machine negate w).step ⟨.sign, inp, work, out⟩ = some ⟨.marker b .empty, inp.move .right, work, out⟩ :=
  read_step negate .sign _ b before tail emitted inp work out hc (by decide) (by cases b <;> rfl)

theorem marker_step (negate negative b : Bool) (m : Magnitude) (before tail emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before (b :: tail) emitted inp work out) :
    (machine negate w).step ⟨.marker negative m, inp, work, out⟩ =
      some ⟨(if b then .payload negative m else .emit negative m 0), inp.move .right, work, out⟩ :=
  read_step negate (.marker negative m) _ b before tail emitted inp work out hc (by intro h; cases h) (by cases b <;> rfl)

theorem payload_step (negate negative b : Bool) (m : Magnitude) (before tail emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before (b :: tail) emitted inp work out) :
    (machine negate w).step ⟨.payload negative m, inp, work, out⟩ =
      some ⟨.marker negative (push m b), inp.move .right, work, out⟩ :=
  read_step negate (.payload negative m) _ b before tail emitted inp work out hc (by intro h; cases h) (by cases b <;> rfl)

theorem eof_step (negate : Bool) (q q' : State) (hq : q ≠ .done) (before emitted : List Bool)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before [] emitted inp work out)
    (ha : action negate q Γ.blank (fun j => (work j).read) out.read =
      allReadBack q' Γ.blank (fun j => (work j).read) out.read) :
    (machine negate w).step ⟨q, inp, work, out⟩ = some ⟨q', inp, work, out⟩ := by
  have hr : inp.read = Γ.blank := by
    rw [Tape.read, hc.head, hc.cells, List.append_nil]
    exact Tape.init_ofBool_cells_ge before before.length le_rfl
  have hδ : (machine negate w).δ q inp.read (fun j => (work j).read) out.read =
      allReadBack q' inp.read (fun j => (work j).read) out.read := by
    rw [hr]
    exact ha
  change action negate q inp.read (fun j => (work j).read) out.read = _ at hδ
  simp only [TM.step, EquationCoefficientMachine.machine, hq, ↓reduceIte]
  rw [hδ]
  change some (⟨q', transitionInput inp, (fun j => transitionTape (work j)), transitionTape out⟩ :
    Cfg w (machine negate w).Q) = _
  obtain ⟨hi, hw, ho⟩ := hc.phase
  rw [hi, hw, ho]
  rfl

theorem unsigned_run (negate negative : Bool) (m : Magnitude) (input before emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before input emitted inp work out) (hs : ∀ j, Parked (work j)) (hr : R work) :
    ∃ inp' work' out' t, t ≤ input.length + 10 ∧
      (machine negate w).reachesIn t ⟨.marker negative m, inp, work, out⟩ ⟨.done, inp', work', out'⟩ ∧
      Cursor (before ++ (scan m input).taken) (scan m input).rest
        (emitted ++ word negate negative (scan m input).magnitude) inp' work' out' ∧
          (∀ j, Parked (work' j)) ∧ R work' := by
  induction input using BitCodec.parseBits.induct generalizing m before inp work out with
  | case1 =>
    have he := eof_step negate (.marker negative m) (.emit negative .bad 0) (by intro h; cases h)
      before emitted inp work out hc rfl
    obtain ⟨inp', work', out', t, ht, hd, hc', hs', hr'⟩ :=
      emit_word negate negative .bad before [] emitted R inp work out hc hs hr
    exact ⟨inp', work', out', t + 1, by simp only [List.length_nil]; omega, .step he hd,
      by simpa only [scan, List.append_nil] using hc', hs', hr'⟩
  | case2 rest =>
    have he := marker_step negate negative false m before rest emitted inp work out hc
    have hcur := InputCursor.consume false hc
    obtain ⟨inp', work', out', t, ht, hd, hc', hs', hr'⟩ :=
      emit_word negate negative m (before ++ [false]) rest emitted R (inp.move .right) work out hcur hs hr
    exact ⟨inp', work', out', t + 1, by simp only [List.length_cons]; omega, .step he hd, hc', hs', hr'⟩
  | case3 =>
    have he := marker_step negate negative true m before [] emitted inp work out hc
    have hcur := InputCursor.consume true hc
    have hf := eof_step negate (.payload negative m) (.emit negative .bad 0) (by intro h; cases h)
      (before ++ [true]) emitted (inp.move .right) work out hcur rfl
    obtain ⟨inp', work', out', t, ht, hd, hc', hs', hr'⟩ :=
      emit_word negate negative .bad (before ++ [true]) [] emitted R (inp.move .right) work out hcur hs hr
    exact ⟨inp', work', out', t + 2, by simp only [List.length_cons, List.length_nil]; omega,
      by simpa only [Nat.add_assoc] using TM.reachesIn.step he (TM.reachesIn.step hf hd), hc', hs', hr'⟩
  | case4 b rest ih =>
    have he := marker_step negate negative true m before (b :: rest) emitted inp work out hc
    have hcur := InputCursor.consume true hc
    have hf := payload_step negate negative b m (before ++ [true]) rest emitted (inp.move .right) work out hcur
    have hcur' := InputCursor.consume b hcur
    obtain ⟨inp', work', out', t, ht, hd, hc', hs', hr'⟩ :=
      ih (push m b) ((before ++ [true]) ++ [b]) ((inp.move .right).move .right) work out hcur' hs hr
    refine ⟨inp', work', out', t + 2, by simp only [List.length_cons]; omega,
      by simpa only [Nat.add_assoc] using TM.reachesIn.step he (TM.reachesIn.step hf hd), ?_, hs', hr'⟩
    simpa only [scan, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using hc'

theorem run (negate : Bool) (input before emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (inp : Tape) (work : Fin w → Tape) (out : Tape) (hc : Cursor before input emitted inp work out)
    (hs : ∀ j, Parked (work j)) (hr : R work) :
    ∃ inp' work' out' t, t ≤ input.length + 11 ∧
      (machine negate w).reachesIn t ⟨.sign, inp, work, out⟩ ⟨.done, inp', work', out'⟩ ∧
      Cursor (before ++ (signed input).2.taken) (signed input).2.rest
        (emitted ++ word negate (signed input).1 (signed input).2.magnitude) inp' work' out' ∧
          (∀ j, Parked (work' j)) ∧ R work' := by
  cases input with
  | nil =>
    have he := eof_step negate .sign (.emit false .bad 0) (by decide) before emitted inp work out hc rfl
    obtain ⟨inp', work', out', t, ht, hd, hc', hs', hr'⟩ :=
      emit_word negate false .bad before [] emitted R inp work out hc hs hr
    exact ⟨inp', work', out', t + 1, by simp only [List.length_nil]; omega, .step he hd,
      by simpa only [signed, List.append_nil] using hc', hs', hr'⟩
  | cons negative rest =>
    have he := sign_step negate negative before rest emitted inp work out hc
    have hcur := InputCursor.consume negative hc
    obtain ⟨inp', work', out', t, ht, hd, hc', hs', hr'⟩ :=
      unsigned_run negate negative .empty rest (before ++ [negative]) emitted R (inp.move .right) work out hcur hs hr
    refine ⟨inp', work', out', t + 1, by simp only [List.length_cons]; omega, .step he hd, ?_, hs', hr'⟩
    simpa only [signed, List.append_assoc, List.singleton_append] using hc'

theorem hoareTime (negate : Bool) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine negate w).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input)
        (emitted ++ BitCodec.integerCode (if negate then -(EquationCoefficientControl.signedValue input) else EquationCoefficientControl.signedValue input))
          inp work out ∧ (∀ j, Parked (work j)) ∧ R work) (input.length + 11) := by
  rintro inp work out ⟨hc, hs, hr⟩
  obtain ⟨inp', work', out', t, ht, hd, hc', hs', hr'⟩ := run negate input before emitted R inp work out hc hs hr
  rw [EquationCoefficientControl.signed_taken, EquationCoefficientControl.signed_rest, EquationCoefficientControl.signed_word] at hc'
  exact ⟨⟨.done, inp', work', out'⟩, t, ht, hd, rfl, hc', hs', hr'⟩

theorem encoded_hoareTime (negate : Bool) (z : ℤ) (hz : z.natAbs ≤ 5)
    (before suffix emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine negate w).HoareTime
      (fun inp work out => Cursor before (BitCodec.integerCode z ++ suffix) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.integerCode z) suffix
        (emitted ++ BitCodec.integerCode (if negate then -z else z)) inp work out ∧
          (∀ j, Parked (work j)) ∧ R work) ((BitCodec.integerCode z ++ suffix).length + 11) := by
  simpa only [NumericCursor.integer_copied_code, NumericCursor.integer_rest_code, EquationCoefficientControl.signed_value_code z hz] using
    hoareTime negate before (BitCodec.integerCode z ++ suffix) emitted R

end JointThermoComplexity.Complexity.EquationCoefficientRun

#print axioms JointThermoComplexity.Complexity.EquationCoefficientRun.hoareTime
#print axioms JointThermoComplexity.Complexity.EquationCoefficientRun.encoded_hoareTime
