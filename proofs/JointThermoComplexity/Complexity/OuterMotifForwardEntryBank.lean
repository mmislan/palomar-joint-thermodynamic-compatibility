module
public import proofs.JointThermoComplexity.Complexity.OuterMotifAccessEntryBank
public import proofs.JointThermoComplexity.Complexity.OuterMotifBankFrame
public import proofs.JointThermoComplexity.Complexity.MotifForwardEntry

set_option autoImplicit false
@[expose] public section

/-! The unchanged total fresh orientation entry retains exact blank production tapes. -/

namespace JointThermoComplexity.Complexity.OuterMotifForwardEntryBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem branch_hoareTime (m : ℕ) (input emitted : List Bool) :
    (MotifForwardBranch.machine (m + 7)).HoareTime
      (fun inp work out => Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) emitted inp work out ∧
        BoxContinuationBranch.Advanced (m + 7) input work ∧ OuterFuelBank.State m work)
      (fun inp work out => Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) emitted inp work out ∧
        MotifForwardBranch.Advanced (m + 7) input work ∧ OuterFuelBank.State m work)
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
    let P : (Fin (m + 22) → Tape) → Prop := fun work =>
      (∀ j, Parked (work j)) ∧ CurrentPins.Kept (m + 7) input work ∧ OuterFuelBank.State m work
    have hn := FixedOutput.hoareTime [] [] input emitted
      (fun work => CurrentPins.Kept (m + 7) input work ∧ OuterFuelBank.State m work)
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 16))
      (MotifForwardPreload.machine (m + 7)) (emitBitsTM []) [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by simpa only [P, BoxContinuationBranch.Advanced, hd, and_assoc] using And.intro hp hbank
    have hflag : (work (RoutedNetworkParser.master (m + 16))).read = Γ.zero := by
      rw [CurrentPins.flag (m + 7) input work hp'.2.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd, List.append_nil] using hdc,
      by simpa only [P, MotifForwardBranch.Advanced, BoxContinuationBranch.Advanced, hd, and_assoc] using hdr⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    let R : (Fin (m + 22) → Tape) → Prop := fun work => MotifBufferMeta.State (m + 7) input work ∧ OuterFuelBank.State m work
    let P := BoxState.Ready (m + 7) input.length Q.speciesCount R
    let A : (Fin (m + 22) → Tape) → Prop := fun work => MotifForwardBranch.Advanced (m + 7) input work ∧ OuterFuelBank.State m work
    have hR : ∀ work work', (∀ j, j ≠ MotifBufferPorts.buffer (m + 7) 2 → work' j = work j) → R work → R work' := by
      rintro work work' hw ⟨hm, hb⟩
      exact ⟨MotifBufferMeta.frame (m + 7) input 2 work work' hw hm, OuterMotifBankFrame.buffer_frame m 2 work work' hw hb⟩
    have hy := MotifForwardPreload.hoareTime (m + 7) Q.speciesCount input Q hd emitted R hR (fun _ h => h.1.1)
    have hy' : (MotifForwardPreload.machine (m + 7)).HoareTime
        (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧ P work)
        (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧ A work)
        (MotifForwardPreload.timeBound input.length) := hy.consequence (fun _ _ _ h => h) (by
      rintro inp work out ⟨hc, hp, hf⟩
      obtain ⟨hready, hbank⟩ := (OuterActivityBoxBankFrame.box_ready_and m input.length Q.speciesCount
        (MotifBufferMeta.State (m + 7) input) (OuterFuelBank.State m) work).mp hp
      exact ⟨hc, by simpa only [MotifForwardBranch.Advanced, hd] using
        (MotifPreparedMasks.ready_iff (m + 7) input Q work).mpr ⟨hready, hf⟩, hbank⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 16)) (MotifForwardPreload.machine (m + 7)) (emitBitsTM [])
      (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted
      P A (MotifForwardPreload.timeBound input.length) hy'
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by
      simpa only [P, R, BoxState.Ready, MotifBufferMeta.State, BoxContinuationBranch.Advanced, hd, and_assoc] using And.intro hp hbank
    have hflag : (work (RoutedNetworkParser.master (m + 16))).read = Γ.one := by
      rw [CurrentPins.flag (m + 7) input work hp'.2.2.2.2.1.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hdc, hdr⟩

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ MotifForwardEntry.timeBound input.length ∧
      (MotifForwardEntry.machine (m + 7)).reachesIn t ((MotifForwardEntry.machine (m + 7)).initCfg input) d ∧
      (MotifForwardEntry.machine (m + 7)).halted d ∧
      Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) (BoxFormulaEntry.code input) d.input d.work d.output ∧
      MotifForwardBranch.Advanced (m + 7) input d.work ∧ OuterFuelBank.State m d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs, hbank⟩ := OuterMotifAccessEntryBank.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs, hdbank⟩ :=
    branch_hoareTime m input (BoxFormulaEntry.code input) c.input c.work c.output ⟨hc, hregs, hbank⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (MotifForwardBranch.machine (m + 7)).reachesIn td
      ⟨(MotifForwardBranch.machine (m + 7)).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    rw [hi, hw, hout]
    exact hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (MotifAccessEntry.machine (m + 7)) (MotifForwardBranch.machine (m + 7)) hcreach hchalt hr
  have hstart : phase1Wrap (MotifAccessEntry.machine (m + 7)) (MotifForwardBranch.machine (m + 7))
      ((MotifAccessEntry.machine (m + 7)).initCfg input) = (MotifForwardEntry.machine (m + 7)).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (MotifAccessEntry.machine (m + 7)) (MotifForwardBranch.machine (m + 7)) d, tc + 1 + td,
    by unfold MotifForwardEntry.timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs, hdbank⟩

end JointThermoComplexity.Complexity.OuterMotifForwardEntryBank

#print axioms JointThermoComplexity.Complexity.OuterMotifForwardEntryBank.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.OuterMotifForwardEntryBank.run
