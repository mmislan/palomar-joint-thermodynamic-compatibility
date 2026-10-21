module
public import proofs.JointThermoComplexity.Complexity.MotifAccessEntryBank
public import proofs.JointThermoComplexity.Complexity.MotifBankFrame
public import proofs.JointThermoComplexity.Complexity.MotifForwardEntry

set_option autoImplicit false
@[expose] public section

/-! The unchanged total fresh orientation entry retains exact blank production tapes. -/

namespace JointThermoComplexity.Complexity.MotifForwardEntryBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem branch_hoareTime (m : ℕ) (input emitted : List Bool) :
    (MotifForwardBranch.machine (m + 5)).HoareTime
      (fun inp work out => Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) emitted inp work out ∧
        BoxContinuationBranch.Advanced (m + 5) input work ∧ ProductionBank.State m work)
      (fun inp work out => Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) emitted inp work out ∧
        MotifForwardBranch.Advanced (m + 5) input work ∧ ProductionBank.State m work)
      (MotifForwardPreload.timeBound input.length + 2) := by
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
      (MotifForwardPreload.machine (m + 5)) (emitBitsTM []) [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by simpa only [P, BoxContinuationBranch.Advanced, hd, and_assoc] using And.intro hp hbank
    have hflag : (work (RoutedNetworkParser.master (m + 14))).read = Γ.zero := by
      rw [CurrentPins.flag (m + 5) input work hp'.2.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd, List.append_nil] using hdc,
      by simpa only [P, MotifForwardBranch.Advanced, BoxContinuationBranch.Advanced, hd, and_assoc] using hdr⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    let R : (Fin (m + 20) → Tape) → Prop := fun work => MotifBufferMeta.State (m + 5) input work ∧ ProductionBank.State m work
    let P := BoxState.Ready (m + 5) input.length Q.speciesCount R
    let A : (Fin (m + 20) → Tape) → Prop := fun work => MotifForwardBranch.Advanced (m + 5) input work ∧ ProductionBank.State m work
    have hR : ∀ work work', (∀ j, j ≠ MotifBufferPorts.buffer (m + 5) 2 → work' j = work j) → R work → R work' := by
      rintro work work' hw ⟨hm, hb⟩
      exact ⟨MotifBufferMeta.frame (m + 5) input 2 work work' hw hm, MotifBankFrame.buffer_frame m 2 work work' hw hb⟩
    have hy := MotifForwardPreload.hoareTime (m + 5) Q.speciesCount input Q hd emitted R hR (fun _ h => h.1.1)
    have hy' : (MotifForwardPreload.machine (m + 5)).HoareTime
        (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧ P work)
        (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧ A work)
        (MotifForwardPreload.timeBound input.length) := hy.consequence (fun _ _ _ h => h) (by
      rintro inp work out ⟨hc, hp, hf⟩
      obtain ⟨hready, hbank⟩ := (ActivityBoxBankFrame.box_ready_and m input.length Q.speciesCount
        (MotifBufferMeta.State (m + 5) input) (ProductionBank.State m) work).mp hp
      exact ⟨hc, by simpa only [MotifForwardBranch.Advanced, hd] using
        (MotifPreparedMasks.ready_iff (m + 5) input Q work).mpr ⟨hready, hf⟩, hbank⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 14)) (MotifForwardPreload.machine (m + 5)) (emitBitsTM [])
      (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted
      P A (MotifForwardPreload.timeBound input.length) hy'
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by
      simpa only [P, R, BoxState.Ready, MotifBufferMeta.State, BoxContinuationBranch.Advanced, hd, and_assoc] using And.intro hp hbank
    have hflag : (work (RoutedNetworkParser.master (m + 14))).read = Γ.one := by
      rw [CurrentPins.flag (m + 5) input work hp'.2.2.2.2.1.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hdc, hdr⟩

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ MotifForwardEntry.timeBound input.length ∧
      (MotifForwardEntry.machine (m + 5)).reachesIn t ((MotifForwardEntry.machine (m + 5)).initCfg input) d ∧
      (MotifForwardEntry.machine (m + 5)).halted d ∧
      Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) (BoxFormulaEntry.code input) d.input d.work d.output ∧
      MotifForwardBranch.Advanced (m + 5) input d.work ∧ ProductionBank.State m d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs, hbank⟩ := MotifAccessEntryBank.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs, hdbank⟩ :=
    branch_hoareTime m input (BoxFormulaEntry.code input) c.input c.work c.output ⟨hc, hregs, hbank⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (MotifForwardBranch.machine (m + 5)).reachesIn td
      ⟨(MotifForwardBranch.machine (m + 5)).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    rw [hi, hw, hout]
    exact hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (MotifAccessEntry.machine (m + 5)) (MotifForwardBranch.machine (m + 5)) hcreach hchalt hr
  have hstart : phase1Wrap (MotifAccessEntry.machine (m + 5)) (MotifForwardBranch.machine (m + 5))
      ((MotifAccessEntry.machine (m + 5)).initCfg input) = (MotifForwardEntry.machine (m + 5)).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (MotifAccessEntry.machine (m + 5)) (MotifForwardBranch.machine (m + 5)) d, tc + 1 + td,
    by unfold MotifForwardEntry.timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs, hdbank⟩

end JointThermoComplexity.Complexity.MotifForwardEntryBank

#print axioms JointThermoComplexity.Complexity.MotifForwardEntryBank.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.MotifForwardEntryBank.run
