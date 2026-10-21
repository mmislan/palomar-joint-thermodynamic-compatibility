module
public import proofs.JointThermoComplexity.Complexity.MotifForwardBranch

set_option autoImplicit false
@[expose] public section

/-! Fresh total input retains common orientations and reaches its first supplied motif. -/

namespace JointThermoComplexity.Complexity.MotifForwardEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def machine (m : ℕ) : TM (m + 15) := seqTM (MotifAccessEntry.machine m) (MotifForwardBranch.machine m)

def timeBound (L : ℕ) : ℕ := MotifAccessEntry.timeBound L + MotifForwardPreload.timeBound L + 3

theorem timeBound_eq (L : ℕ) :
    timeBound L = 384 * L ^ 5 + 1104 * L ^ 4 + 1746 * L ^ 3 + 1784 * L ^ 2 + 1124 * L + 279 := by
  rw [timeBound, MotifAccessEntry.timeBound_eq]
  unfold MotifForwardPreload.timeBound
  ring1

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine m).reachesIn t ((machine m).initCfg input) d ∧
      (machine m).halted d ∧ Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input)
        (BoxFormulaEntry.code input) d.input d.work d.output ∧ MotifForwardBranch.Advanced m input d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs⟩ := MotifAccessEntry.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs⟩ :=
    MotifForwardBranch.hoareTime m input (BoxFormulaEntry.code input) c.input c.work c.output ⟨hc, hregs⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (MotifForwardBranch.machine m).reachesIn td
      ⟨(MotifForwardBranch.machine m).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    rw [hi, hw, hout]
    exact hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (MotifAccessEntry.machine m) (MotifForwardBranch.machine m)
    hcreach hchalt hr
  have hstart : phase1Wrap (MotifAccessEntry.machine m) (MotifForwardBranch.machine m)
      ((MotifAccessEntry.machine m).initCfg input) = (machine m).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (MotifAccessEntry.machine m) (MotifForwardBranch.machine m) d, tc + 1 + td,
    by unfold timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs⟩

end JointThermoComplexity.Complexity.MotifForwardEntry

#print axioms JointThermoComplexity.Complexity.MotifForwardEntry.timeBound_eq
#print axioms JointThermoComplexity.Complexity.MotifForwardEntry.run
