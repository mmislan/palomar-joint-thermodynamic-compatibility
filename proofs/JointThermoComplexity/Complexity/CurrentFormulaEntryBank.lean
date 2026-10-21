module
public import proofs.JointThermoComplexity.Complexity.NetworkCircuitEntryBank
public import proofs.JointThermoComplexity.Complexity.CurrentContinuationBank
public import proofs.JointThermoComplexity.Complexity.CurrentFormulaEntry

set_option autoImplicit false
@[expose] public section

/-! The original total fresh circuit/current formula entry retains the five production tapes as exact blank registers. -/

namespace JointThermoComplexity.Complexity.CurrentFormulaEntryBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem branch_hoareTime (m : ℕ) (input emitted : List Bool) :
    (CurrentContinuationBranch.machine (m + 5)).HoareTime
      (fun inp work out => Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) emitted inp work out ∧
        NetworkCircuitEntry.Advanced (m + 5) input work ∧ ProductionBank.State m work)
      (fun inp work out => Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input)
        (emitted ++ CurrentContinuationBranch.word input) inp work out ∧ CurrentContinuationBranch.Advanced (m + 5) input work ∧ ProductionBank.State m work)
      (CurrentContinuation.timeBound input.length + 2) := by
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
      (∀ j, Parked (work j)) ∧ NetworkPins.Kept (m + 5) input work ∧ ProductionBank.State m work
    have hn := FixedOutput.hoareTime [] [] input emitted
      (fun work => NetworkPins.Kept (m + 5) input work ∧ ProductionBank.State m work)
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 14)) (CurrentContinuation.machine (m + 5)) (emitBitsTM [])
      [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by simpa only [P, NetworkCircuitEntry.Advanced, hd, and_assoc] using And.intro hp hbank
    have hflag : (work (RoutedNetworkParser.master (m + 14))).read = Γ.zero := by
      rw [CurrentPins.flag (m + 5) input work (CurrentPins.of_network (m + 5) input work hp'.2.1), ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hs, hk, hdbank⟩ := hb inp work out
      ⟨⟨by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, CurrentContinuationBranch.word, hd] using hdc,
      by simpa only [CurrentContinuationBranch.Advanced, hd] using And.intro hs (CurrentPins.of_network (m + 5) input d.work hk), hdbank⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    let P : (Fin (m + 20) → Tape) → Prop := fun work => NetworkEmitReady.Ready (m + 5) input.length
      (Q.speciesCount + Q.reactionCount) (NetworkMembership.gates Q.network) Q.speciesCount (NetworkPins.Kept (m + 5) input) work ∧
      IsReg Q.reactionCount (work (ReactionFuel.slot (m + 5))) ∧ ProductionBank.State m work
    let A : (Fin (m + 20) → Tape) → Prop := fun work => CurrentContinuationBranch.Advanced (m + 5) input work ∧ ProductionBank.State m work
    have hy := CurrentContinuationBank.hoareTime m input Q hd emitted
    have hy' : (CurrentContinuation.machine (m + 5)).HoareTime
        (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q) emitted inp work out ∧ P work)
        (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
          (emitted ++ CurrentContinuationBranch.word input) inp work out ∧ A work) (CurrentContinuation.timeBound input.length) :=
      hy.consequence (fun _ _ _ ⟨hc, hp, _, hb⟩ => ⟨hc, hp, hb⟩) (by
        rintro inp work out ⟨hc, hp, hf, hb⟩
        exact ⟨by simpa only [CurrentContinuationBranch.word, hd] using hc,
          by simpa only [CurrentContinuationBranch.Advanced, hd] using And.intro hp hf, hb⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 14)) (CurrentContinuation.machine (m + 5)) (emitBitsTM [])
      (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q) emitted
      (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q) (emitted ++ CurrentContinuationBranch.word input)
      P A (CurrentContinuation.timeBound input.length) hy'
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by simpa only [P, NetworkCircuitEntry.Advanced, hd, and_assoc] using And.intro hp hbank
    have hk : NetworkPins.Kept (m + 5) input work := hp'.1.2.2.2.2.2.2.2.2
    have hflag : (work (RoutedNetworkParser.master (m + 14))).read = Γ.one := by
      rw [CurrentPins.flag (m + 5) input work (CurrentPins.of_network (m + 5) input work hk), ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hp, hdbank⟩ := hb inp work out
      ⟨⟨by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hdc, hp, hdbank⟩

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ CurrentFormulaEntry.timeBound input.length ∧
      (CurrentFormulaEntry.machine (m + 5)).reachesIn t ((CurrentFormulaEntry.machine (m + 5)).initCfg input) d ∧
      (CurrentFormulaEntry.machine (m + 5)).halted d ∧
      Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) (CurrentFormulaEntry.code input) d.input d.work d.output ∧
      CurrentContinuationBranch.Advanced (m + 5) input d.work ∧ ProductionBank.State m d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs, hbank⟩ := NetworkCircuitEntryBank.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs, hdbank⟩ :=
    branch_hoareTime m input (NetworkCircuitEntry.code input) c.input c.work c.output ⟨hc, hregs, hbank⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (CurrentContinuationBranch.machine (m + 5)).reachesIn td
      ⟨(CurrentContinuationBranch.machine (m + 5)).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, hout] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (NetworkCircuitEntry.machine (m + 5)) (CurrentContinuationBranch.machine (m + 5)) hcreach hchalt hr
  have hstart : phase1Wrap (NetworkCircuitEntry.machine (m + 5)) (CurrentContinuationBranch.machine (m + 5))
      ((NetworkCircuitEntry.machine (m + 5)).initCfg input) = (CurrentFormulaEntry.machine (m + 5)).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (NetworkCircuitEntry.machine (m + 5)) (CurrentContinuationBranch.machine (m + 5)) d, tc + 1 + td,
    by unfold CurrentFormulaEntry.timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs, hdbank⟩

end JointThermoComplexity.Complexity.CurrentFormulaEntryBank

#print axioms JointThermoComplexity.Complexity.CurrentFormulaEntryBank.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.CurrentFormulaEntryBank.run
