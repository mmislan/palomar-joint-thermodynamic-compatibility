module
public import proofs.JointThermoComplexity.Complexity.ActivityContinuationBranch
public import proofs.JointThermoComplexity.Complexity.ActivitySuffix

set_option autoImplicit false
@[expose] public section

/-! Fresh total emission now includes the complete activity-positivity block of the constraint suffix. -/

namespace JointThermoComplexity.Complexity.ActivityFormulaEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CircuitSerialization

def machine (m : ℕ) : TM (m + 15) := seqTM (CurrentFormulaEntry.machine m) (ActivityContinuationBranch.machine m)

def timeBound (L : ℕ) : ℕ := CurrentFormulaEntry.timeBound L + ActivityStart.timeBound L + 3

theorem timeBound_eq (L : ℕ) :
    timeBound L = 384 * L ^ 5 + 1104 * L ^ 4 + 1614 * L ^ 3 + 1492 * L ^ 2 + 794 * L + 208 := by
  rw [timeBound, CurrentFormulaEntry.timeBound_eq]
  unfold ActivityStart.timeBound
  ring1

def code (input : List Bool) : List Bool := CurrentFormulaEntry.code input ++ ActivityContinuationBranch.word input

theorem code_prefix (input : List Bool) : ∃ rest, (NetworkCodec.toSentence input).code = code input ++ rest := by
  cases hd : NetworkCodec.decode input with
  | none =>
    refine ⟨[], ?_⟩
    simp only [code, CurrentFormulaEntry.code, NetworkCircuitEntry.code, FormulaStart.code, NetworkCircuitEntry.word,
      CurrentContinuationBranch.word, ActivityContinuationBranch.word, NetworkCodec.toSentence, hd, FalseOutput.sentence, List.append_nil]
  | some Q =>
    refine ⟨(ActivitySuffix.formula Q).code, ?_⟩
    have hc : (NetworkCodec.toSentence input).code = CurrentFormulaEntry.code input ++
        (NetworkFormula.constraintsFormula Q.network (NetworkMembership.activityIndex Q.network) (NetworkMembership.currentIndex Q.network)).code := by
      simpa only [CurrentFormulaEntry.code, NetworkCircuitEntry.code, FormulaStart.code, NetworkCircuitEntry.word,
        CurrentContinuationBranch.word, NetworkCodec.toSentence, hd, FormulaPrefix.suffix,
        RealSyntax.Formula.code, conjunctionTag, List.append_assoc] using FormulaPrefix.sentence_code Q
    rw [hc, ActivitySuffix.constraints_code]
    simp only [code, ActivityContinuationBranch.word, hd, List.append_assoc]

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine m).reachesIn t ((machine m).initCfg input) d ∧
      (machine m).halted d ∧ Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input)
        (code input) d.input d.work d.output ∧ ActivityContinuationBranch.Advanced m input d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs⟩ := CurrentFormulaEntry.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs⟩ :=
    ActivityContinuationBranch.hoareTime m input (CurrentFormulaEntry.code input) c.input c.work c.output ⟨hc, hregs⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (ActivityContinuationBranch.machine m).reachesIn td
      ⟨(ActivityContinuationBranch.machine m).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, hout] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (CurrentFormulaEntry.machine m) (ActivityContinuationBranch.machine m) hcreach hchalt hr
  have hstart : phase1Wrap (CurrentFormulaEntry.machine m) (ActivityContinuationBranch.machine m)
      ((CurrentFormulaEntry.machine m).initCfg input) = (machine m).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (CurrentFormulaEntry.machine m) (ActivityContinuationBranch.machine m) d, tc + 1 + td,
    by unfold timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs⟩

end JointThermoComplexity.Complexity.ActivityFormulaEntry

#print axioms JointThermoComplexity.Complexity.ActivityFormulaEntry.timeBound_eq
#print axioms JointThermoComplexity.Complexity.ActivityFormulaEntry.code_prefix
#print axioms JointThermoComplexity.Complexity.ActivityFormulaEntry.run
