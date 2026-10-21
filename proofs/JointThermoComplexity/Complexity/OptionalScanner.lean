module
public import proofs.JointThermoComplexity.Complexity.OptionalFrame

set_option autoImplicit false
@[expose] public section

/-! Exact optional-record codec agreement and actual tag-dispatch time. -/

namespace JointThermoComplexity.Complexity.OptionalScanner
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ScannerSpec OptionalMachine FiniteCodec FieldControl

variable {w : ℕ} {α : Type} {A : Codec α}

theorem runs {S : Control A} {tm : TM w} {master flag : Fin w}
    {Env : (Fin w → Tape) → Prop} {T : ℕ → ℕ}
    (hscan : Runs S tm master flag Env T) (hmono : Monotone T) (hne : tm.qstart ≠ tm.qhalt)
    (hm : master ≠ flag)
    (hEnv : ∀ work work', (∀ j, j ≠ master → j ≠ flag → work' j = work j) → Env work → Env work') :
    Runs (RecordControl.optional S) (OptionalMachine.machine tm master flag) master flag Env (fun L => T L + 1) := by
  intro initial before input emitted R hR inp work out hpre
  rcases hpre with ⟨hc, hf, hmh, hmr, he, hstate⟩
  have htagged (good : Bool) :
      Env (taggedWork work master flag good) ∧ R (taggedWork work master flag good) := by
    have hothers : ∀ j, j ≠ master → j ≠ flag → taggedWork work master flag good j = work j := by
      intro j hjm hjf
      exact OptionalFrame.other work master flag good j hjf hjm (hc.works j).1
    exact ⟨hEnv work _ hothers he, hR work _ hothers hstate⟩
  cases input with
  | nil =>
    have hi : inp.read = Γ.blank := by
      simp [Tape.read, hc.head, hc.cells, Tape.init_ofBool_cells_ge before before.length le_rfl]
    let d : Cfg w (State tm.Q) := ⟨.done, transitionInput inp, taggedWork work master flag false, transitionTape out⟩
    have hdin : d.input = inp := transitionInput_eq_self (by simp [hi])
    have hdout : d.output = out := transitionTape_eq_self hc.output_read
    have hcursor : Cursor before [] emitted d.input d.work d.output := by
      simpa only [hdin, hdout] using OptionalFrame.cursor hc master flag hm false hf hmh
    refine ⟨d, 1, by change 1 ≤ T [].length + 1; omega,
      .step (eof_step tm master flag ⟨.tag, inp, work, out⟩ rfl hi) .zero, rfl, ?_⟩
    simpa only [RecordControl.optional, List.append_nil, Bool.and_false, Γ.ofBool] using
      (show Cursor before [] emitted d.input d.work d.output ∧ (d.work flag).head = 1 ∧
        (d.work master).head = 1 ∧ (d.work master).read = Γ.zero ∧ Env d.work ∧ R d.work from
        ⟨hcursor, OptionalFrame.flag_head work master flag false (hc.works flag).1 hf,
          OptionalFrame.master_bad_head work master flag hm (hc.works master).1 hmh,
          OptionalFrame.master_bad_read work master flag hm (hc.works master).1 hmh,
          (htagged false).1, (htagged false).2⟩)
  | cons bit rest =>
    have hindex : before.length < (before ++ bit :: rest).length := by simp
    have hread : inp.read = Γ.ofBool bit := by
      rw [Tape.read, hc.head, hc.cells, Tape.init_ofBool_cells_lt _ before.length hindex]
      simp
    cases bit with
    | false =>
      let d : Cfg w (State tm.Q) := ⟨.done, inp.move .right, taggedWork work master flag true,
        out.writeAndMove Γ.zero .right⟩
      have hready := (OptionalFrame.cursor hc master flag hm true hf hmh).works
      have hhead : d.input.head = before.length + [false].length + 1 := by simp [d, Tape.move, hc.head]
      have hcursor : Cursor (before ++ [false]) rest (emitted ++ [false]) d.input d.work d.output :=
        NumericCursor.advance hc rfl rfl hhead hready (Tape.hasBinaryPrefix_write_bit false hc.tapePrefix)
          (Tape.hasBinaryPrefix_write_bit_cell0 false hc.tapePrefix hc.zero)
      have hmaster := OptionalFrame.master_good work master flag hm (hc.works master).1
      refine ⟨d, 1, by change 1 ≤ T (false :: rest).length + 1; omega,
        .step (none_step tm master flag ⟨.tag, inp, work, out⟩ rfl hread) .zero, rfl, ?_⟩
      simpa only [RecordControl.optional, Bool.and_true] using
        (show Cursor (before ++ [false]) rest (emitted ++ [false]) d.input d.work d.output ∧
          (d.work flag).head = 1 ∧ (d.work master).head = 1 ∧
          (d.work master).read = Γ.ofBool initial ∧ Env d.work ∧ R d.work from
          ⟨hcursor, OptionalFrame.flag_head work master flag true (hc.works flag).1 hf,
            by simpa only [d, hmaster] using hmh, by simpa only [d, hmaster] using hmr,
            (htagged true).1, (htagged true).2⟩)
    | true =>
      let c : Cfg w tm.Q := ⟨tm.qstart, inp.move .right, work, out.writeAndMove Γ.one .right⟩
      have hwork : (fun j => transitionTape (work j)) = work := by
        funext j
        exact transitionTape_eq_self (hc.works j).1
      have hstep : (OptionalMachine.machine tm master flag).step ⟨.tag, inp, work, out⟩ =
          some (wrap tm master flag c) := by
        have he : (⟨.body tm.qstart, inp.move .right,
            (fun j => transitionTape (work j)), out.writeAndMove Γ.one .right⟩ : Cfg w (State tm.Q)) =
            wrap tm master flag c := by
          apply Cfg.ext
          · simp [wrap, wrapState, c, hne]
          · rfl
          · exact hwork
          · rfl
        exact (some_step tm master flag ⟨.tag, inp, work, out⟩ rfl hread).trans (congrArg some he)
      have hhead : c.input.head = before.length + [true].length + 1 := by simp [c, Tape.move, hc.head]
      have hcursor : Cursor (before ++ [true]) rest (emitted ++ [true]) c.input c.work c.output :=
        NumericCursor.advance hc rfl rfl hhead hc.works (Tape.hasBinaryPrefix_write_bit true hc.tapePrefix)
          (Tape.hasBinaryPrefix_write_bit_cell0 true hc.tapePrefix hc.zero)
      obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdf, hdm, hdv, hde, hdr⟩ :=
        hscan initial (before ++ [true]) rest (emitted ++ [true]) R hR c.input work c.output
          ⟨hcursor, hf, hmh, hmr, he, hstate⟩
      have hlen : rest.length ≤ (true :: rest).length := by simp
      have htime := ht.trans (hmono hlen)
      refine ⟨wrap tm master flag d, t + 1, by change t + 1 ≤ T (true :: rest).length + 1; omega,
        .step hstep (body_reaches tm master flag hreach), body_halted tm master flag hhalt, ?_⟩
      refine ⟨?_, hdf, hdm, hdv, hde, hdr⟩
      simpa only [RecordControl.optional, List.append_assoc, List.singleton_append, wrap] using hdcur

end JointThermoComplexity.Complexity.OptionalScanner

#print axioms JointThermoComplexity.Complexity.OptionalScanner.runs
