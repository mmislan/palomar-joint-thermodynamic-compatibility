module
public import proofs.JointThermoComplexity.Complexity.NetworkCircuitBodyBank
public import proofs.JointThermoComplexity.Complexity.NetworkCircuitEntry

set_option autoImplicit false
@[expose] public section

/-! The unchanged fresh guarded circuit entry returns its original output and a proved blank production bank. -/

namespace JointThermoComplexity.Complexity.NetworkCircuitEntryBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem branch_hoareTime (m : ℕ) (input emitted : List Bool) :
    (NetworkCircuitEntry.branch (m + 5)).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        FormulaStart.Registers (m + 12) input work ∧ ProductionBank.State m work)
      (fun inp work out => Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input)
        (emitted ++ NetworkCircuitEntry.word input) inp work out ∧
        NetworkCircuitEntry.Advanced (m + 5) input work ∧ ProductionBank.State m work)
      (NetworkCircuitBody.timeBound input.length + 2) := by
  let P : (Fin (m + 20) → Tape) → Prop := fun work =>
    (∀ j, Parked (work j)) ∧ FormulaStart.Registers (m + 12) input work ∧ ProductionBank.State m work
  let A : (Fin (m + 20) → Tape) → Prop := fun work => NetworkCircuitEntry.Advanced (m + 5) input work ∧ ProductionBank.State m work
  cases hd : NetworkCodec.decode input with
  | none =>
    have ha : NetworkInputControl.accepted input = false := by
      cases he : NetworkInputControl.accepted input with
      | false => rfl
      | true =>
        obtain ⟨Q, hQ⟩ := (NetworkInputControl.status_iff_decode input).mp he
        rw [hd] at hQ
        cases hQ
    have hn := FixedOutput.hoareTime [] [] input emitted
      (fun work => FormulaStart.Registers (m + 12) input work ∧ ProductionBank.State m work)
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 14))
      (NetworkCircuitBody.machine (m + 5)) (emitBitsTM []) [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hs, ⟨hg, ho, hbi, hk, hsp⟩, hbank⟩
    have hflag : (work (RoutedNetworkParser.master (m + 14))).read = Γ.zero := by
      simpa only [CountAppend.oldWork, RoutedNetworkParser.master, ha, Γ.ofBool] using hk.2.1
    obtain ⟨d, t, ht, hr, hh, hdc, hds, ⟨hdg, hdo, hdb, hdk, _⟩, hdbank⟩ :=
      hb inp work out ⟨⟨hc, hs, ⟨hg, ho, hbi, hk, hsp⟩, hbank⟩, hflag⟩
    exact ⟨d, t, by unfold NetworkCircuitBody.timeBound; omega, hr, hh,
      by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, NetworkCircuitEntry.word, hd] using hdc,
      by simpa only [NetworkCircuitEntry.Advanced, hd] using
        (And.intro hds (show NetworkPins.Kept (m + 5) input d.work from ⟨hdg, hdo, hdb, hdk⟩)), hdbank⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    have hy := NetworkCircuitBodyBank.hoareTime m input Q hd emitted
    have hy' : (NetworkCircuitBody.machine (m + 5)).HoareTime
        (fun inp work out => Cursor [] input emitted inp work out ∧ P work)
        (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
          (emitted ++ NetworkCircuitEntry.word input) inp work out ∧ A work) (NetworkCircuitBody.timeBound input.length) :=
      hy.consequence (fun _ _ _ h => h) (by
        rintro inp work out ⟨hc, hp, hf, hb⟩
        exact ⟨by simpa only [NetworkCircuitEntry.word, hd] using hc,
          by simpa only [NetworkCircuitEntry.Advanced, hd] using And.intro hp hf, hb⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 14))
      (NetworkCircuitBody.machine (m + 5)) (emitBitsTM []) [] input emitted
      (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
      (emitted ++ NetworkCircuitEntry.word input) P A (NetworkCircuitBody.timeBound input.length) hy'
    rintro inp work out ⟨hc, hs, ⟨hg, ho, hbi, hk, hsp⟩, hbank⟩
    have hflag : (work (RoutedNetworkParser.master (m + 14))).read = Γ.one := by
      simpa only [CountAppend.oldWork, RoutedNetworkParser.master, ha, Γ.ofBool] using hk.2.1
    obtain ⟨d, t, ht, hr, hh, hdc, hp, hdbank⟩ := hb inp work out ⟨⟨hc, hs, ⟨hg, ho, hbi, hk, hsp⟩, hbank⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hdc, hp, hdbank⟩

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ NetworkCircuitEntry.timeBound input.length ∧
      (NetworkCircuitEntry.machine (m + 5)).reachesIn t ((NetworkCircuitEntry.machine (m + 5)).initCfg input) d ∧
      (NetworkCircuitEntry.machine (m + 5)).halted d ∧
      Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) (NetworkCircuitEntry.code input) d.input d.work d.output ∧
      NetworkCircuitEntry.Advanced (m + 5) input d.work ∧ ProductionBank.State m d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hs, hregs⟩ := FormulaStart.run (m + 12) input
  have hbank := ProductionBank.of_spare m c.work hregs.2.2.2.2
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs, hdbank⟩ :=
    branch_hoareTime m input (FormulaStart.code input) c.input c.work c.output ⟨hc, hs, hregs, hbank⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (NetworkCircuitEntry.branch (m + 5)).reachesIn td
      ⟨(NetworkCircuitEntry.branch (m + 5)).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, hout] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (FormulaStart.machine (m + 12)) (NetworkCircuitEntry.branch (m + 5)) hcreach hchalt hr
  have hstart : phase1Wrap (FormulaStart.machine (m + 12)) (NetworkCircuitEntry.branch (m + 5))
      ((FormulaStart.machine (m + 12)).initCfg input) = (NetworkCircuitEntry.machine (m + 5)).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (FormulaStart.machine (m + 12)) (NetworkCircuitEntry.branch (m + 5)) d, tc + 1 + td,
    by unfold NetworkCircuitEntry.timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs, hdbank⟩

end JointThermoComplexity.Complexity.NetworkCircuitEntryBank

#print axioms JointThermoComplexity.Complexity.NetworkCircuitEntryBank.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.NetworkCircuitEntryBank.run
