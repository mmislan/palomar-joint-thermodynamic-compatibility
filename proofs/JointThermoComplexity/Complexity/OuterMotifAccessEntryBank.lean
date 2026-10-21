module
public import proofs.JointThermoComplexity.Complexity.OuterBoxFormulaEntryBank
public import proofs.JointThermoComplexity.Complexity.MotifAccessEntry

set_option autoImplicit false
@[expose] public section

/-! The original fresh motif access preserves the exact production bank on every input. -/

namespace JointThermoComplexity.Complexity.OuterMotifAccessEntryBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem branch_hoareTime (m : ℕ) (input emitted : List Bool) :
    (MotifAccessBranch.machine (m + 7)).HoareTime
      (fun inp work out => Cursor (BoxContinuationBranch.before input) (BoxContinuationBranch.remaining input) emitted inp work out ∧
        BoxContinuationBranch.Advanced (m + 7) input work ∧ OuterFuelBank.State m work)
      (fun inp work out => Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) emitted inp work out ∧
        BoxContinuationBranch.Advanced (m + 7) input work ∧ OuterFuelBank.State m work)
      (MotifAccess.timeBound input.length + 2) := by
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
      (MotifAccess.machine (m + 7)) (emitBitsTM []) [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by simpa only [P, BoxContinuationBranch.Advanced, hd, and_assoc] using And.intro hp hbank
    have hflag : (work (RoutedNetworkParser.master (m + 16))).read = Γ.zero := by
      rw [CurrentPins.flag (m + 7) input work hp'.2.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [BoxContinuationBranch.before, BoxContinuationBranch.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd, List.append_nil] using hdc,
      by simpa only [P, BoxContinuationBranch.Advanced, hd, and_assoc] using hdr⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    let P : (Fin (m + 22) → Tape) → Prop := fun work => BoxContinuationBranch.Advanced (m + 7) input work ∧ OuterFuelBank.State m work
    have hy := MotifAccess.hoareTime (m + 7) input Q hd emitted (fun work _ => P work)
    have hy' : (MotifAccess.machine (m + 7)).HoareTime
        (fun inp work out => Cursor input [] emitted inp work out ∧ P work)
        (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧ P work)
        (MotifAccess.timeBound input.length) := hy.consequence (by
      rintro inp work out ⟨hc, hp⟩
      have hready : BoxState.Ready (m + 7) input.length Q.speciesCount
          (fun work => CurrentPins.Kept (m + 7) input work ∧ BoxRegisters.State (m + 7) input work) work := by
        simpa only [BoxContinuationBranch.Advanced, hd] using hp.1
      exact ⟨hc, hready.1, hready.2.2.2.2.1, hp⟩)
      (fun _ _ _ ⟨hc, _, _, hp⟩ => ⟨hc, hp⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 16)) (MotifAccess.machine (m + 7)) (emitBitsTM [])
      input [] emitted (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted P P (MotifAccess.timeBound input.length) hy'
    rintro inp work out ⟨hc, hp, hbank⟩
    have hready : BoxState.Ready (m + 7) input.length Q.speciesCount
        (fun work => CurrentPins.Kept (m + 7) input work ∧ BoxRegisters.State (m + 7) input work) work := by
      simpa only [BoxContinuationBranch.Advanced, hd] using hp
    have hflag : (work (RoutedNetworkParser.master (m + 16))).read = Γ.one := by
      rw [CurrentPins.flag (m + 7) input work hready.2.2.2.2.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [BoxContinuationBranch.before, BoxContinuationBranch.remaining, hd] using hc, ⟨hp, hbank⟩⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hdc, hdr⟩

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ MotifAccessEntry.timeBound input.length ∧
      (MotifAccessEntry.machine (m + 7)).reachesIn t ((MotifAccessEntry.machine (m + 7)).initCfg input) d ∧
      (MotifAccessEntry.machine (m + 7)).halted d ∧
      Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) (BoxFormulaEntry.code input) d.input d.work d.output ∧
      BoxContinuationBranch.Advanced (m + 7) input d.work ∧ OuterFuelBank.State m d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs, hbank⟩ := OuterBoxFormulaEntryBank.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs, hdbank⟩ :=
    branch_hoareTime m input (BoxFormulaEntry.code input) c.input c.work c.output ⟨hc, hregs, hbank⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (MotifAccessBranch.machine (m + 7)).reachesIn td
      ⟨(MotifAccessBranch.machine (m + 7)).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    rw [hi, hw, hout]
    exact hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (BoxFormulaEntry.machine (m + 7)) (MotifAccessBranch.machine (m + 7)) hcreach hchalt hr
  have hstart : phase1Wrap (BoxFormulaEntry.machine (m + 7)) (MotifAccessBranch.machine (m + 7))
      ((BoxFormulaEntry.machine (m + 7)).initCfg input) = (MotifAccessEntry.machine (m + 7)).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (BoxFormulaEntry.machine (m + 7)) (MotifAccessBranch.machine (m + 7)) d, tc + 1 + td,
    by unfold MotifAccessEntry.timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs, hdbank⟩

end JointThermoComplexity.Complexity.OuterMotifAccessEntryBank

#print axioms JointThermoComplexity.Complexity.OuterMotifAccessEntryBank.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.OuterMotifAccessEntryBank.run
