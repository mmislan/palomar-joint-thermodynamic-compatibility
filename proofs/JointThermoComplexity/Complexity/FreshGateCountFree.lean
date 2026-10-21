module
public import proofs.JointThermoComplexity.Complexity.FreshGateCount
public import proofs.JointThermoComplexity.Complexity.ParserCountReadyFree

set_option autoImplicit false
@[expose] public section

/-! Total gate-count preparation retains a proven blank bank for later address arithmetic. -/

namespace JointThermoComplexity.Complexity.FreshGateCountFree
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem run (n : ℕ) (input : List Bool) :
    ∃ d t, t ≤ FreshGateCount.timeBound input.length ∧
      (FreshGateCount.machine n).reachesIn t ((FreshGateCount.machine n).initCfg input) d ∧
      (FreshGateCount.machine n).halted d ∧ Cursor [] input [] d.input d.work d.output ∧ (∀ j, Parked (d.work j)) ∧
      IsReg (GateCountValue.count input) (d.work (RoutedNetworkParser.raw n)) ∧
      ParserRegisters.Kept n input (CountAppend.oldWork d.work) ∧ NetworkParserFree.Free n (CountAppend.oldWork d.work) := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hs, hz, hk, hfree⟩ := ParserCountReadyFree.run n input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdsafe, hdreg, hdkept, hdfree⟩ :=
    CountDispatch.hoareTime n input [] (NetworkParserFree.Free n) c.input c.work c.output ⟨hc, hs, hz, hk, hfree⟩
  obtain ⟨hi, hw, ho⟩ := hc.phase
  have hr : (CountDispatch.machine n).reachesIn td
      ⟨(CountDispatch.machine n).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, ho] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (ParserCountReady.machine n) (CountDispatch.machine n) hcreach hchalt hr
  have hstart : phase1Wrap (ParserCountReady.machine n) (CountDispatch.machine n)
      ((ParserCountReady.machine n).initCfg input) = (FreshGateCount.machine n).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (ParserCountReady.machine n) (CountDispatch.machine n) d, tc + 1 + td,
    by unfold FreshGateCount.timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt,
    hdcur, hdsafe, hdreg, hdkept, hdfree⟩

end JointThermoComplexity.Complexity.FreshGateCountFree

#print axioms JointThermoComplexity.Complexity.FreshGateCountFree.run
