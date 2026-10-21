module
public import proofs.JointThermoComplexity.Complexity.CurrentFormulaEntryBank
public import proofs.JointThermoComplexity.Complexity.ActivityContinuationBank
public import proofs.JointThermoComplexity.Complexity.ActivityFormulaEntry

set_option autoImplicit false
@[expose] public section

/-! Total fresh positivity output retains the production bank on valid and malformed inputs. -/

namespace JointThermoComplexity.Complexity.ActivityFormulaEntryBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem branch_hoareTime (m : ℕ) (input emitted : List Bool) :
    (ActivityContinuationBranch.machine (m + 5)).HoareTime
      (fun inp work out => Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) emitted inp work out ∧
        CurrentContinuationBranch.Advanced (m + 5) input work ∧ ProductionBank.State m work)
      (fun inp work out => Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input)
        (emitted ++ ActivityContinuationBranch.word input) inp work out ∧
        ActivityContinuationBranch.Advanced (m + 5) input work ∧ ProductionBank.State m work)
      (ActivityStart.timeBound input.length + 2) := by
  cases hd : NetworkCodec.decode input with
  | none =>
    have ha : NetworkInputControl.accepted input = false := by
      cases he : NetworkInputControl.accepted input with
      | false => rfl
      | true =>
        obtain ⟨Q, hQ⟩ := (NetworkInputControl.status_iff_decode input).mp he
        rw [hd] at hQ
        cases hQ
    let P : (Fin (m + 20) → Tape) → Prop := fun work =>
      (∀ j, Parked (work j)) ∧ CurrentPins.Kept (m + 5) input work ∧ ProductionBank.State m work
    have hn := FixedOutput.hoareTime [] [] input emitted
      (fun work => CurrentPins.Kept (m + 5) input work ∧ ProductionBank.State m work)
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 14))
      (ActivityStart.machine (m + 5)) (emitBitsTM []) [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by simpa only [P, CurrentContinuationBranch.Advanced, hd, and_assoc] using And.intro hp hbank
    have hflag : (work (RoutedNetworkParser.master (m + 14))).read = Γ.zero := by
      rw [CurrentPins.flag (m + 5) input work hp'.2.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hs, hk, hdbank⟩ := hb inp work out
      ⟨⟨by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, ActivityContinuationBranch.word, hd] using hdc,
      by simpa only [ActivityContinuationBranch.Advanced, hd] using And.intro hs hk, hdbank⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    let P : (Fin (m + 20) → Tape) → Prop := fun work => CurrentReady.Ready (m + 5) input.length
      (NetworkMembership.arity Q.network) (Q.speciesCount + Q.reactionCount) Q.speciesCount
      (CurrentResources.State (m + 5) input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot (m + 5))) ∧ ProductionBank.State m work
    let A : (Fin (m + 20) → Tape) → Prop := fun work => ActivityContinuationBranch.Advanced (m + 5) input work ∧ ProductionBank.State m work
    have hy := ActivityContinuationBank.hoareTime m input Q hd (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) emitted
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 14)) (ActivityStart.machine (m + 5)) (emitBitsTM [])
      (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) emitted
      (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) (emitted ++ ActivityContinuationBranch.word input)
      P A (ActivityStart.timeBound input.length) (by simpa only [P, A, ActivityContinuationBranch.word, ActivityContinuationBranch.Advanced, hd, and_assoc] using hy)
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by simpa only [P, CurrentContinuationBranch.Advanced, hd, and_assoc] using And.intro hp hbank
    have hres : CurrentResources.State (m + 5) input work := hp'.1.2.2.2.2.2.2
    have hflag : (work (RoutedNetworkParser.master (m + 14))).read = Γ.one := by
      rw [CurrentPins.flag (m + 5) input work hres.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hpost⟩ := hb inp work out ⟨⟨hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh, hdc, hpost⟩

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ ActivityFormulaEntry.timeBound input.length ∧
      (ActivityFormulaEntry.machine (m + 5)).reachesIn t ((ActivityFormulaEntry.machine (m + 5)).initCfg input) d ∧
      (ActivityFormulaEntry.machine (m + 5)).halted d ∧
      Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) (ActivityFormulaEntry.code input) d.input d.work d.output ∧
      ActivityContinuationBranch.Advanced (m + 5) input d.work ∧ ProductionBank.State m d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs, hbank⟩ := CurrentFormulaEntryBank.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs, hdbank⟩ :=
    branch_hoareTime m input (CurrentFormulaEntry.code input) c.input c.work c.output ⟨hc, hregs, hbank⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (ActivityContinuationBranch.machine (m + 5)).reachesIn td
      ⟨(ActivityContinuationBranch.machine (m + 5)).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, hout] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (CurrentFormulaEntry.machine (m + 5)) (ActivityContinuationBranch.machine (m + 5)) hcreach hchalt hr
  have hstart : phase1Wrap (CurrentFormulaEntry.machine (m + 5)) (ActivityContinuationBranch.machine (m + 5))
      ((CurrentFormulaEntry.machine (m + 5)).initCfg input) = (ActivityFormulaEntry.machine (m + 5)).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (CurrentFormulaEntry.machine (m + 5)) (ActivityContinuationBranch.machine (m + 5)) d, tc + 1 + td,
    by unfold ActivityFormulaEntry.timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs, hdbank⟩

end JointThermoComplexity.Complexity.ActivityFormulaEntryBank

#print axioms JointThermoComplexity.Complexity.ActivityFormulaEntryBank.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.ActivityFormulaEntryBank.run
