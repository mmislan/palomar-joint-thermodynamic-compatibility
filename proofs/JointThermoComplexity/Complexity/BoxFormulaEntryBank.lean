module
public import proofs.JointThermoComplexity.Complexity.ActivityFormulaEntryBank
public import proofs.JointThermoComplexity.Complexity.BoxContinuationBank
public import proofs.JointThermoComplexity.Complexity.BoxFormulaEntry

set_option autoImplicit false
@[expose] public section

/-! The original total fresh formula prefix through rational boxes retains exact blank production tapes. -/

namespace JointThermoComplexity.Complexity.BoxFormulaEntryBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem branch_hoareTime (m : ℕ) (input emitted : List Bool) :
    (BoxContinuationBranch.machine (m + 5)).HoareTime
      (fun inp work out => Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) emitted inp work out ∧
        ActivityContinuationBranch.Advanced (m + 5) input work ∧ ProductionBank.State m work)
      (fun inp work out => Cursor (BoxContinuationBranch.before input) (BoxContinuationBranch.remaining input)
        (emitted ++ BoxContinuationBranch.word input) inp work out ∧
        BoxContinuationBranch.Advanced (m + 5) input work ∧ ProductionBank.State m work)
      (BoxContinuation.timeBound input.length + 2) := by
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
      (BoxContinuation.machine (m + 5)) (emitBitsTM []) [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by simpa only [P, ActivityContinuationBranch.Advanced, hd, and_assoc] using And.intro hp hbank
    have hflag : (work (RoutedNetworkParser.master (m + 14))).read = Γ.zero := by
      rw [CurrentPins.flag (m + 5) input work hp'.2.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hs, hk, hdbank⟩ := hb inp work out
      ⟨⟨by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [BoxContinuationBranch.before, BoxContinuationBranch.remaining, BoxContinuationBranch.word, hd, List.append_nil] using hdc,
      by simpa only [BoxContinuationBranch.Advanced, hd] using And.intro hs hk, hdbank⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    let P : (Fin (m + 20) → Tape) → Prop := fun work =>
      CurrentReady.Ready (m + 5) input.length (NetworkMembership.arity Q.network) Q.speciesCount Q.speciesCount
        (CurrentResources.State (m + 5) input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot (m + 5))) ∧ ProductionBank.State m work
    let A : (Fin (m + 20) → Tape) → Prop := fun work => BoxContinuationBranch.Advanced (m + 5) input work ∧ ProductionBank.State m work
    have hbefore : (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) ++ NetworkTallyData.tail Q = input := by
      simpa only [List.append_assoc] using (NetworkCircuitBody.input_split input Q hd).symm
    have hy := BoxContinuationBank.hoareTime m input Q hd (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) emitted
    have hy' : (BoxContinuation.machine (m + 5)).HoareTime
        (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q) emitted inp work out ∧ P work)
        (fun inp work out => Cursor input [] (emitted ++ BoxContinuationBranch.word input) inp work out ∧ A work)
        (BoxContinuation.timeBound input.length) := hy.consequence
      (fun _ _ _ ⟨hc, hp, _, hb⟩ => ⟨hc, hp, hb⟩) (by
        rintro inp work out ⟨hc, hr, hb⟩
        exact ⟨by simpa only [hbefore, BoxContinuationBranch.word, hd] using hc,
          by simpa only [BoxContinuationBranch.Advanced, hd] using hr, hb⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 14)) (BoxContinuation.machine (m + 5)) (emitBitsTM [])
      (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q) emitted
      input [] (emitted ++ BoxContinuationBranch.word input) P A (BoxContinuation.timeBound input.length) hy'
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by simpa only [P, ActivityContinuationBranch.Advanced, hd, and_assoc] using And.intro hp hbank
    have hk : CurrentPins.Kept (m + 5) input work := by
      rcases hp'.1 with ⟨_, _, _, _, _, _, hk, _⟩
      exact hk
    have hflag : (work (RoutedNetworkParser.master (m + 14))).read = Γ.one := by
      rw [CurrentPins.flag (m + 5) input work hk, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [BoxContinuationBranch.before, BoxContinuationBranch.remaining, hd] using hdc, hdr⟩

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ BoxFormulaEntry.timeBound input.length ∧
      (BoxFormulaEntry.machine (m + 5)).reachesIn t ((BoxFormulaEntry.machine (m + 5)).initCfg input) d ∧
      (BoxFormulaEntry.machine (m + 5)).halted d ∧
      Cursor (BoxContinuationBranch.before input) (BoxContinuationBranch.remaining input) (BoxFormulaEntry.code input) d.input d.work d.output ∧
      BoxContinuationBranch.Advanced (m + 5) input d.work ∧ ProductionBank.State m d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs, hbank⟩ := ActivityFormulaEntryBank.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs, hdbank⟩ :=
    branch_hoareTime m input (ActivityFormulaEntry.code input) c.input c.work c.output ⟨hc, hregs, hbank⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (BoxContinuationBranch.machine (m + 5)).reachesIn td
      ⟨(BoxContinuationBranch.machine (m + 5)).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    rw [hi, hw, hout]
    exact hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (ActivityFormulaEntry.machine (m + 5)) (BoxContinuationBranch.machine (m + 5)) hcreach hchalt hr
  have hstart : phase1Wrap (ActivityFormulaEntry.machine (m + 5)) (BoxContinuationBranch.machine (m + 5))
      ((ActivityFormulaEntry.machine (m + 5)).initCfg input) = (BoxFormulaEntry.machine (m + 5)).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (ActivityFormulaEntry.machine (m + 5)) (BoxContinuationBranch.machine (m + 5)) d, tc + 1 + td,
    by unfold BoxFormulaEntry.timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs, hdbank⟩

end JointThermoComplexity.Complexity.BoxFormulaEntryBank

#print axioms JointThermoComplexity.Complexity.BoxFormulaEntryBank.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.BoxFormulaEntryBank.run
