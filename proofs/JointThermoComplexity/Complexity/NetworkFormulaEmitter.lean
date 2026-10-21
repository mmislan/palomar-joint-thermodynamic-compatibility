module
public import proofs.JointThermoComplexity.Complexity.MotifContinuationBranch

set_option autoImplicit false
@[expose] public section

/-! The complete actual fixed binary TM emits the original total network-to-sentence map on every input. -/

namespace JointThermoComplexity.Complexity.NetworkFormulaEmitter
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def machine (m : ℕ) : TM (m + 22) := seqTM (OuterFuelFreshEntry.machine m) (MotifContinuationBranch.machine m)

def timeBound (L : ℕ) : ℕ := OuterFuelFreshEntry.timeBound L + MotifCoreBlock.timeBound L + 3

theorem timeBound_eq (L : ℕ) : timeBound L =
    4 * L ^ 6 + 436 * L ^ 5 + 1288 * L ^ 4 + 1998 * L ^ 3 + 1976 * L ^ 2 + 1252 * L + 326 := by
  rw [timeBound, OuterFuelFreshEntry.timeBound_eq]
  unfold MotifCoreBlock.timeBound
  ring1

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine m).reachesIn t ((machine m).initCfg input) d ∧
      (machine m).halted d ∧ Cursor [] input (NetworkCodec.toSentence input).code d.input d.work d.output ∧
      MotifContinuationBranch.Final m input d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs⟩ := OuterFuelFreshEntry.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs⟩ :=
    MotifContinuationBranch.hoareTime m input (BoxFormulaEntry.code input) c.input c.work c.output ⟨hc, hregs⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (MotifContinuationBranch.machine m).reachesIn td
      ⟨(MotifContinuationBranch.machine m).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    rw [hi, hw, hout]
    exact hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (OuterFuelFreshEntry.machine m) (MotifContinuationBranch.machine m)
    hcreach hchalt hr
  have hstart : phase1Wrap (OuterFuelFreshEntry.machine m) (MotifContinuationBranch.machine m)
      ((OuterFuelFreshEntry.machine m).initCfg input) = (machine m).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (OuterFuelFreshEntry.machine m) (MotifContinuationBranch.machine m) d, tc + 1 + td,
    by unfold timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt,
    by
      change Cursor [] input (NetworkCodec.toSentence input).code d.input d.work d.output
      simpa only [MotifFormulaSuffix.full_code] using hdcur, hdregs⟩

theorem computesInTime (m : ℕ) :
    (machine m).ComputesInTime (fun input => (NetworkCodec.toSentence input).code) timeBound := by
  intro input
  obtain ⟨d, t, ht, hr, hh, hc, _⟩ := run m input
  exact ⟨d, t, ht, hr, hh, hc.tapePrefix.2.1, hc.tapePrefix.2.2 _ le_rfl⟩

end JointThermoComplexity.Complexity.NetworkFormulaEmitter

#print axioms JointThermoComplexity.Complexity.NetworkFormulaEmitter.timeBound_eq
#print axioms JointThermoComplexity.Complexity.NetworkFormulaEmitter.run
#print axioms JointThermoComplexity.Complexity.NetworkFormulaEmitter.computesInTime
