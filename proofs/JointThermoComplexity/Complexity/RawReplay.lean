module
public import proofs.JointThermoComplexity.Complexity.RawEmitScan
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Repeated literal emission from an end-parked binary buffer with exact work-tape restoration. -/

namespace JointThermoComplexity.Complexity.RawReplay
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryEmitMachine

variable {w : ℕ}

def machine (idx : Fin w) : TM w := seqTM (rewindWorkTM idx) (RawEmitMachine.machine idx)

theorem hoareTime (idx : Fin w) (bits before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work idx).HasBinaryPrefix bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ bits) inp work out ∧
        (work idx).HasBinaryPrefix bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (2 * bits.length + 5) := by
  rintro inp work out ⟨hc, hbits, hz, hr⟩
  let P : Tape → (Fin w → Tape) → Tape → Prop := fun inp' work' out' =>
    inp' = inp ∧ out' = out ∧ (work' idx).cells = (work idx).cells ∧
      ∀ j, j ≠ idx → work' j = work j
  have hP : ∀ (inp' : Tape) (work' : Fin w → Tape) (out' : Tape)
      (inp'' : Tape) (work'' : Fin w → Tape) (out'' : Tape),
      P inp' work' out' → (work'' idx).cells = (work' idx).cells → (work'' idx).head = 1 →
      (∀ j, j ≠ idx → work'' j = work' j) → inp'' = inp' → out''.cells = out'.cells →
      out''.head = out'.head → P inp'' work'' out'' := by
    rintro inp' work' out' inp'' work'' out'' ⟨hinp, hout, hcells, hothers⟩ hc' _ hw' hi' hoc hoh
    exact ⟨hi'.trans hinp, (Tape.ext hoh hoc).trans hout, hc'.trans hcells,
      fun j hj => (hw' j hj).trans (hothers j hj)⟩
  have hcontent : (work idx).HasBinaryContent bits := hbits.2
  obtain ⟨c, tc, htc, hcreach, hchalt, hchead, hcp⟩ :=
    rewindWorkTM_hoareTime_frame idx (bits.length + 1) hP inp work out
      ⟨hz, hcontent.cells_ne_start, hbits.1.le, hc.input_read, hc.output_read,
        by rw [hc.tapePrefix.1]; omega, (fun j _ => hc.works j), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hcc : (c.work idx).HasBinaryContent bits := by
    simpa only [Tape.HasBinaryContent, hcp.2.2.1] using hcontent
  have hcurc : Cursor before input emitted c.input c.work c.output := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hcp.1] using hc.cells
    · simpa only [hcp.1] using hc.head
    · intro j
      by_cases hj : j = idx
      · subst j
        exact ⟨by rw [Tape.read, hchead]; exact hcc.cells_ne_start 1 (by omega), by rw [hchead]⟩
      · simpa only [hcp.2.2.2 j hj] using hc.works j
    · simpa only [hcp.2.1] using hc.tapePrefix
    · simpa only [hcp.2.1] using hc.zero
  let start : Cfg w State := ⟨.read, c.input, c.work, c.output⟩
  obtain ⟨d, td, htd, hdreach, hdhalt, hdin, hdcells, hdhead, hdother, hdp, hdz⟩ :=
    RawEmitScan.scan bits [] emitted idx start rfl hcc hchead hcurc.input_read
      (fun j _ => (hcurc.works j).1) hcurc.tapePrefix hcurc.zero
  have hdhead' : (d.work idx).head = bits.length + 1 := by
    simpa only [List.length_nil, Nat.zero_add] using hdhead
  have hdwork : d.work = work := by
    funext j
    by_cases hj : j = idx
    · subst j
      apply Tape.ext (hdhead'.trans hbits.1.symm)
      exact hdcells.trans hcp.2.2.1
    · exact (hdother j hj).trans (hcp.2.2.2 j hj)
  have hcurd : Cursor before input (emitted ++ bits) d.input d.work d.output := by
    refine ⟨?_, ?_, ?_, hdp, hdz⟩
    · simpa only [hdin, start, hcp.1] using hc.cells
    · simpa only [hdin, start, hcp.1] using hc.head
    · simpa only [hdwork] using hc.works
  have hreach₂ : (RawEmitMachine.machine idx).reachesIn td
      ⟨(RawEmitMachine.machine idx).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    obtain ⟨hi, hw, ho⟩ := hcurc.phase
    rw [hi, hw, ho]
    exact hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (rewindWorkTM idx) (RawEmitMachine.machine idx)
    hcreach hchalt hreach₂
  refine ⟨phase2Wrap (rewindWorkTM idx) (RawEmitMachine.machine idx) d, tc + 1 + td,
    by omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hcurd, ?_, ?_, ?_⟩
  · simpa only [phase2Wrap, hdwork] using hbits
  · simpa only [phase2Wrap, hdwork] using hz
  · simpa only [phase2Wrap, hdwork] using hr

end JointThermoComplexity.Complexity.RawReplay

#print axioms JointThermoComplexity.Complexity.RawReplay.hoareTime
