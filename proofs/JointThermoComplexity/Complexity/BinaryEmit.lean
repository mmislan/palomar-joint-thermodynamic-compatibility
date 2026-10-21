module
public import proofs.JointThermoComplexity.Complexity.BinaryEmitScan
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementRun
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Exact canonical payload output with every work tape returned unchanged. -/

namespace JointThermoComplexity.Complexity.BinaryEmit
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (idx : Fin w) : TM w := seqTM (BinaryEmitMachine.machine idx) (rewindWorkTM idx)

theorem hoareTime (idx : Fin w) (bits : List Bool) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ BitCodec.encodeBits bits) inp work out ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (3 * bits.length + 5) := by
  rintro inp work out ⟨hc, hbits, hz, hr⟩
  obtain ⟨d, td, htd, hreachd, hhaltd, hid, hcd, hhd, hwd, hpd, hzd⟩ :=
    BinaryEmitScan.scan bits [] emitted idx ⟨.read, inp, work, out⟩ rfl hbits.2 hbits.1 hc.input_read
      (fun j _ => (hc.works j).1) hc.tapePrefix hc.zero
  let P : Tape → (Fin w → Tape) → Tape → Prop := fun inp' work' out' =>
    inp' = d.input ∧ out' = d.output ∧ (work' idx).cells = (d.work idx).cells ∧
      ∀ j, j ≠ idx → work' j = d.work j
  have hP : ∀ (inp' : Tape) (work' : Fin w → Tape) (out' : Tape)
      (inp'' : Tape) (work'' : Fin w → Tape) (out'' : Tape),
      P inp' work' out' → (work'' idx).cells = (work' idx).cells → (work'' idx).head = 1 →
      (∀ j, j ≠ idx → work'' j = work' j) → inp'' = inp' → out''.cells = out'.cells →
      out''.head = out'.head → P inp'' work'' out'' := by
    rintro inp' work' out' inp'' work'' out'' ⟨hinp, hout, hcells, hothers⟩ hc' _ hw' hi' hoc hoh
    exact ⟨hi'.trans hinp, (Tape.ext hoh hoc).trans hout, hc'.trans hcells,
      fun j hj => (hw' j hj).trans (hothers j hj)⟩
  have hcontent : (d.work idx).HasBinaryContent bits := by simpa only [Tape.HasBinaryContent, hcd] using hbits.2
  have hdinput : d.input.read ≠ Γ.start := by simpa only [hid] using hc.input_read
  have hdout : d.output.read ≠ Γ.start := by
    have hb : d.output.read = Γ.blank := by
      rw [Tape.read, hpd.1]
      exact hpd.2.2 (emitted ++ BitCodec.encodeBits bits).length le_rfl
    simp [hb]
  have hhead : (d.work idx).head ≤ bits.length + 1 := by simpa using hhd.le
  obtain ⟨e, te, hte, hreache, hhalte, hehead, hp⟩ :=
    rewindWorkTM_hoareTime_frame idx (bits.length + 1) hP d.input d.work d.output
      ⟨by simpa only [hcd] using hz, hcontent.cells_ne_start, hhead, hdinput, hdout,
        by rw [hpd.1]; omega,
        (fun j hj => by simpa only [hwd j hj] using hc.works j), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hwork : e.work = work := by
    funext j
    by_cases hj : j = idx
    · subst j
      apply Tape.ext (hehead.trans hbits.1.symm)
      exact hp.2.2.1.trans hcd
    · exact (hp.2.2.2 j hj).trans (hwd j hj)
  have hcurd : Cursor before input (emitted ++ BitCodec.encodeBits bits) e.input e.work e.output := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hp.1, hid] using hc.cells
    · simpa only [hp.1, hid] using hc.head
    · simpa only [hwork] using hc.works
    · simpa only [hp.2.1] using hpd
    · simpa only [hp.2.1] using hzd
  have hreach₂ : (rewindWorkTM idx).reachesIn te
      ⟨(rewindWorkTM idx).qstart, transitionInput d.input, (fun j => transitionTape (d.work j)), transitionTape d.output⟩ e := by
    have hi' := transitionInput_eq_self hdinput
    have ho' := transitionTape_eq_self hdout
    have hw' : (fun j => transitionTape (d.work j)) = d.work := by
      funext j
      apply transitionTape_eq_self
      by_cases hj : j = idx
      · subst j
        exact hcontent.cells_ne_start _ (by rw [hhd]; simp)
      · simpa only [hwd j hj] using (hc.works j).1
    simpa only [hi', ho', hw'] using hreache
  have hreach := seqTM_reachesIn_of_reachesIn (BinaryEmitMachine.machine idx) (rewindWorkTM idx) hreachd hhaltd hreach₂
  refine ⟨phase2Wrap (BinaryEmitMachine.machine idx) (rewindWorkTM idx) e, td + 1 + te, by omega,
    hreach, (phase2Wrap_halted_iff _ _ e).mpr hhalte, hcurd, ?_, ?_, ?_⟩
  · simpa only [phase2Wrap, hwork] using hbits
  · simpa only [phase2Wrap, hwork] using hz
  · simpa only [phase2Wrap, hwork] using hr

theorem natural_hoareTime (idx : Fin w) (value : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ BinaryIncrementRun.Register value (work idx) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ BitCodec.naturalCode value) inp work out ∧
        BinaryIncrementRun.Register value (work idx) ∧ R work) (3 * value.bits.length + 5) := by
  simpa only [BinaryIncrementRun.Register, BitCodec.naturalCode, and_assoc] using hoareTime idx value.bits before input emitted R

end JointThermoComplexity.Complexity.BinaryEmit

#print axioms JointThermoComplexity.Complexity.BinaryEmit.natural_hoareTime
