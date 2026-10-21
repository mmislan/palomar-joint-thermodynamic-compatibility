module
public import proofs.JointThermoComplexity.Complexity.MotifAccessBranch

set_option autoImplicit false
@[expose] public section

/-! A fresh total input produces the checked box prefix and reaches its supplied motifs. -/

namespace JointThermoComplexity.Complexity.MotifAccessEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def machine (m : ℕ) : TM (m + 15) := seqTM (BoxFormulaEntry.machine m) (MotifAccessBranch.machine m)

def timeBound (L : ℕ) : ℕ := BoxFormulaEntry.timeBound L + MotifAccess.timeBound L + 3

theorem timeBound_eq (L : ℕ) :
    timeBound L = 384 * L ^ 5 + 1104 * L ^ 4 + 1744 * L ^ 3 + 1772 * L ^ 2 + 1091 * L + 248 := by
  rw [timeBound, BoxFormulaEntry.timeBound_eq]
  unfold MotifAccess.timeBound
  ring1

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine m).reachesIn t ((machine m).initCfg input) d ∧
      (machine m).halted d ∧ Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input)
        (BoxFormulaEntry.code input) d.input d.work d.output ∧ BoxContinuationBranch.Advanced m input d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs⟩ := BoxFormulaEntry.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs⟩ :=
    MotifAccessBranch.hoareTime m input (BoxFormulaEntry.code input) c.input c.work c.output ⟨hc, hregs⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (MotifAccessBranch.machine m).reachesIn td
      ⟨(MotifAccessBranch.machine m).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    rw [hi, hw, hout]
    exact hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (BoxFormulaEntry.machine m) (MotifAccessBranch.machine m)
    hcreach hchalt hr
  have hstart : phase1Wrap (BoxFormulaEntry.machine m) (MotifAccessBranch.machine m)
      ((BoxFormulaEntry.machine m).initCfg input) = (machine m).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (BoxFormulaEntry.machine m) (MotifAccessBranch.machine m) d, tc + 1 + td,
    by unfold timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs⟩

end JointThermoComplexity.Complexity.MotifAccessEntry

#print axioms JointThermoComplexity.Complexity.MotifAccessEntry.timeBound_eq
#print axioms JointThermoComplexity.Complexity.MotifAccessEntry.run
