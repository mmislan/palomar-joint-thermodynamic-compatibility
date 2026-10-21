module
public import proofs.JointThermoComplexity.Complexity.CurrentContinuationBranch

set_option autoImplicit false
@[expose] public section

/-! A fresh total actual machine emits the complete circuit and current-equation prefix of the target sentence. -/

namespace JointThermoComplexity.Complexity.CurrentFormulaEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CircuitSerialization

def machine (m : ℕ) : TM (m + 15) := seqTM (NetworkCircuitEntry.machine m) (CurrentContinuationBranch.machine m)

def timeBound (L : ℕ) : ℕ := NetworkCircuitEntry.timeBound L + CurrentContinuation.timeBound L + 3

theorem timeBound_eq (L : ℕ) :
    timeBound L = 384 * L ^ 5 + 1104 * L ^ 4 + 1582 * L ^ 3 + 1436 * L ^ 2 + 749 * L + 189 := by
  rw [timeBound, NetworkCircuitEntry.timeBound_eq, CurrentContinuation.timeBound_eq]
  ring1

def code (input : List Bool) : List Bool := NetworkCircuitEntry.code input ++ CurrentContinuationBranch.word input

theorem code_prefix (input : List Bool) : ∃ rest, (NetworkCodec.toSentence input).code = code input ++ rest := by
  cases hd : NetworkCodec.decode input with
  | none =>
    refine ⟨[], ?_⟩
    simp only [code, NetworkCircuitEntry.code, FormulaStart.code, NetworkCircuitEntry.word,
      CurrentContinuationBranch.word, NetworkCodec.toSentence, hd, FalseOutput.sentence, List.append_nil]
  | some Q =>
    refine ⟨(NetworkFormula.constraintsFormula Q.network (NetworkMembership.activityIndex Q.network)
      (NetworkMembership.currentIndex Q.network)).code, ?_⟩
    simpa only [code, NetworkCircuitEntry.code, FormulaStart.code, NetworkCircuitEntry.word,
      CurrentContinuationBranch.word, NetworkCodec.toSentence, hd, FormulaPrefix.suffix,
      RealSyntax.Formula.code, conjunctionTag, List.append_assoc] using FormulaPrefix.sentence_code Q

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine m).reachesIn t ((machine m).initCfg input) d ∧
      (machine m).halted d ∧ Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input)
        (code input) d.input d.work d.output ∧ CurrentContinuationBranch.Advanced m input d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs⟩ := NetworkCircuitEntry.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs⟩ :=
    CurrentContinuationBranch.hoareTime m input (NetworkCircuitEntry.code input) c.input c.work c.output ⟨hc, hregs⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (CurrentContinuationBranch.machine m).reachesIn td
      ⟨(CurrentContinuationBranch.machine m).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, hout] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (NetworkCircuitEntry.machine m) (CurrentContinuationBranch.machine m) hcreach hchalt hr
  have hstart : phase1Wrap (NetworkCircuitEntry.machine m) (CurrentContinuationBranch.machine m)
      ((NetworkCircuitEntry.machine m).initCfg input) = (machine m).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (NetworkCircuitEntry.machine m) (CurrentContinuationBranch.machine m) d, tc + 1 + td,
    by unfold timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs⟩

end JointThermoComplexity.Complexity.CurrentFormulaEntry

#print axioms JointThermoComplexity.Complexity.CurrentFormulaEntry.timeBound_eq
#print axioms JointThermoComplexity.Complexity.CurrentFormulaEntry.code_prefix
#print axioms JointThermoComplexity.Complexity.CurrentFormulaEntry.run
