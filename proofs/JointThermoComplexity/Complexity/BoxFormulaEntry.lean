module
public import proofs.JointThermoComplexity.Complexity.BoxContinuationBranch
public import proofs.JointThermoComplexity.Complexity.BoxSuffix

set_option autoImplicit false
@[expose] public section

/-! Fresh total circuit/current/activity/box emission, with only the exact motif constraint suffix left. -/

namespace JointThermoComplexity.Complexity.BoxFormulaEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CircuitSerialization

def machine (m : ℕ) : TM (m + 15) := seqTM (ActivityFormulaEntry.machine m) (BoxContinuationBranch.machine m)

def timeBound (L : ℕ) : ℕ := ActivityFormulaEntry.timeBound L + BoxContinuation.timeBound L + 3

theorem timeBound_eq (L : ℕ) :
    timeBound L = 384 * L ^ 5 + 1104 * L ^ 4 + 1742 * L ^ 3 + 1764 * L ^ 2 + 1079 * L + 233 := by
  rw [timeBound, ActivityFormulaEntry.timeBound_eq, BoxContinuation.timeBound_eq]
  ring1

def code (input : List Bool) : List Bool := ActivityFormulaEntry.code input ++ BoxContinuationBranch.word input

theorem code_prefix (input : List Bool) : ∃ rest, (NetworkCodec.toSentence input).code = code input ++ rest := by
  cases hd : NetworkCodec.decode input with
  | none =>
    refine ⟨[], ?_⟩
    simp only [code, ActivityFormulaEntry.code, CurrentFormulaEntry.code, NetworkCircuitEntry.code, FormulaStart.code,
      NetworkCircuitEntry.word, CurrentContinuationBranch.word, ActivityContinuationBranch.word, BoxContinuationBranch.word,
      NetworkCodec.toSentence, hd, FalseOutput.sentence, List.append_nil]
  | some Q =>
    refine ⟨(BoxSuffix.formula Q).code, ?_⟩
    have hcurrent : (NetworkCodec.toSentence input).code = CurrentFormulaEntry.code input ++
        (NetworkFormula.constraintsFormula Q.network (NetworkMembership.activityIndex Q.network)
          (NetworkMembership.currentIndex Q.network)).code := by
      simpa only [CurrentFormulaEntry.code, NetworkCircuitEntry.code, FormulaStart.code, NetworkCircuitEntry.word,
        CurrentContinuationBranch.word, NetworkCodec.toSentence, hd, FormulaPrefix.suffix,
        RealSyntax.Formula.code, conjunctionTag, List.append_assoc] using FormulaPrefix.sentence_code Q
    have hc : (NetworkCodec.toSentence input).code = ActivityFormulaEntry.code input ++ (ActivitySuffix.formula Q).code := by
      rw [hcurrent, ActivitySuffix.constraints_code]
      simp only [ActivityFormulaEntry.code, ActivityContinuationBranch.word, hd, List.append_assoc]
    rw [hc, BoxSuffix.activity_suffix_code]
    simp only [code, BoxContinuationBranch.word, hd, List.append_assoc]

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine m).reachesIn t ((machine m).initCfg input) d ∧
      (machine m).halted d ∧ Cursor (BoxContinuationBranch.before input) (BoxContinuationBranch.remaining input)
        (code input) d.input d.work d.output ∧ BoxContinuationBranch.Advanced m input d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs⟩ := ActivityFormulaEntry.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs⟩ :=
    BoxContinuationBranch.hoareTime m input (ActivityFormulaEntry.code input) c.input c.work c.output ⟨hc, hregs⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (BoxContinuationBranch.machine m).reachesIn td
      ⟨(BoxContinuationBranch.machine m).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    rw [hi, hw, hout]
    exact hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (ActivityFormulaEntry.machine m) (BoxContinuationBranch.machine m)
    hcreach hchalt hr
  have hstart : phase1Wrap (ActivityFormulaEntry.machine m) (BoxContinuationBranch.machine m)
      ((ActivityFormulaEntry.machine m).initCfg input) = (machine m).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (ActivityFormulaEntry.machine m) (BoxContinuationBranch.machine m) d, tc + 1 + td,
    by unfold timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs⟩

end JointThermoComplexity.Complexity.BoxFormulaEntry

#print axioms JointThermoComplexity.Complexity.BoxFormulaEntry.timeBound_eq
#print axioms JointThermoComplexity.Complexity.BoxFormulaEntry.code_prefix
#print axioms JointThermoComplexity.Complexity.BoxFormulaEntry.run
