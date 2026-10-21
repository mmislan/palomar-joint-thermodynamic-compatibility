module
public import proofs.JointThermoComplexity.Complexity.UnaryReset

set_option autoImplicit false
@[expose] public section

/-! Clear a binary buffer from any bounded off-marker head, including its end after a replay. -/

namespace JointThermoComplexity.Complexity.BinaryBufferReset
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (idx : Fin w) : TM w := seqTM (rewindWorkTM idx) (clearWorkTM idx)

theorem hoareTime (idx : Fin w) (bits before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryContent bits ∧ (work idx).cells 0 = Γ.start ∧
        (work idx).head ≤ bits.length + 1 ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work idx) ∧ R work) (3 * bits.length + 9) := by
  rintro inp work out ⟨hc, hsafe, hb, hz, hhead, hr⟩
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
  obtain ⟨c, tc, htc, hcreach, hchalt, hchead, hcp⟩ :=
    rewindWorkTM_hoareTime_frame idx (bits.length + 1) hP inp work out
      ⟨hz, hb.cells_ne_start, hhead, hc.input_read, hc.output_read,
        by rw [hc.tapePrefix.1]; omega, (fun j _ => hc.works j), rfl, rfl, rfl, fun _ _ => rfl⟩
  have hcc : (c.work idx).HasBinaryContent bits := by
    simpa only [Tape.HasBinaryContent, hcp.2.2.1] using hb
  have hcsafe : ∀ j, Parked (c.work j) := by
    intro j
    by_cases hj : j = idx
    · subst j; exact ⟨by rw [hchead], hcc.cells_ne_start⟩
    · rw [hcp.2.2.2 j hj]; exact hsafe j
  have hcurc : Cursor before input emitted c.input c.work c.output :=
    ⟨by simpa only [hcp.1] using hc.cells, by simpa only [hcp.1] using hc.head,
      (fun j => ⟨(hcsafe j).read_ne_start, (hcsafe j).1⟩),
      by simpa only [hcp.2.1] using hc.tapePrefix, by simpa only [hcp.2.1] using hc.zero⟩
  have hclear := BinaryClear.hoareTime idx bits before input emitted R hR
  have hs := SafeExecution.hoareTime (clearWorkTM idx) _ _ _ hclear (by
    rintro inp' work' out' ⟨hc', _, _⟩ j
    exact (hc'.works j).2)
  obtain ⟨d, td, htd, hdreach, hdhalt, ⟨hdcur, hdb, hdr⟩, hdsafe⟩ := hs c.input c.work c.output
    ⟨⟨hcurc, ⟨hchead, hcc⟩, by simpa only [hcp.2.2.1] using hz,
      hR work c.work hcp.2.2.2 hr⟩, hcsafe⟩
  have hreg : IsReg 0 (d.work idx) := CountTape.register_of_string
    (by simpa only [Nat.zero_bits, List.replicate_zero] using hdb.1) hdb.2
  have hreach₂ : (clearWorkTM idx).reachesIn td
      ⟨(clearWorkTM idx).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    obtain ⟨hi, hw, ho⟩ := hcurc.phase
    rw [hi, hw, ho]
    exact hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (rewindWorkTM idx) (clearWorkTM idx) hcreach hchalt hreach₂
  exact ⟨phase2Wrap (rewindWorkTM idx) (clearWorkTM idx) d, tc + 1 + td, by omega,
    hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdsafe, hreg, hdr⟩

end JointThermoComplexity.Complexity.BinaryBufferReset

#print axioms JointThermoComplexity.Complexity.BinaryBufferReset.hoareTime
