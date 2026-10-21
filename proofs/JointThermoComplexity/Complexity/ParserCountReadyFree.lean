module
public import proofs.JointThermoComplexity.Complexity.ParserCountReady
public import proofs.JointThermoComplexity.Complexity.NetworkReadyFree

set_option autoImplicit false
@[expose] public section

/-! The parser's scratch bank stays blank when its copied prefix is cleared. -/

namespace JointThermoComplexity.Complexity.ParserCountReadyFree
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem run (n : ℕ) (input : List Bool) :
    ∃ d t, t ≤ ParserCountReady.timeBound input.length ∧
      (ParserCountReady.machine n).reachesIn t ((ParserCountReady.machine n).initCfg input) d ∧
      (ParserCountReady.machine n).halted d ∧ Cursor [] input [] d.input d.work d.output ∧ (∀ j, Parked (d.work j)) ∧
      IsReg 0 (d.work (RoutedNetworkParser.raw n)) ∧ ParserRegisters.Kept n input (CountAppend.oldWork d.work) ∧
      NetworkParserFree.Free n (CountAppend.oldWork d.work) := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hret, hfree⟩ := NetworkReadyFree.run n input
  have hs : ∀ j, Parked (c.work j) := fun j => TapeSafety.fresh_work_parked hcreach j (hc.works j).2
  let RP : (Fin (n + 6) → Tape) → Prop := fun work =>
    ParserRegisters.Kept n input (CountAppend.oldWork work) ∧ NetworkParserFree.Free n (CountAppend.oldWork work)
  have hRP : ∀ work work', (∀ j, j ≠ RoutedNetworkParser.raw n → work' j = work j) → RP work → RP work' := by
    intro work work' hw hp
    change ParserRegisters.Kept n input (CountAppend.oldWork work') ∧ NetworkParserFree.Free n (CountAppend.oldWork work')
    rw [CountOffset.oldWork_eq hw]
    exact hp
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdsafe, hdreg, hdkept, hdfree⟩ :=
    PrefixClear.hoareTime (RoutedNetworkParser.raw n) (NetworkInputControl.copied input) [] input [] RP hRP
      c.input c.work c.output ⟨hc, hs, hret.1, hret.2.1, ParserRegisters.kept_of_retained n input c.work hret, hfree⟩
  obtain ⟨hi, hw, ho⟩ := hc.phase
  have hr : (PrefixClear.machine (RoutedNetworkParser.raw n)).reachesIn td
      ⟨(PrefixClear.machine (RoutedNetworkParser.raw n)).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, ho] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (NetworkReady.machine n)
    (PrefixClear.machine (RoutedNetworkParser.raw n)) hcreach hchalt hr
  have hstart : phase1Wrap (NetworkReady.machine n) (PrefixClear.machine (RoutedNetworkParser.raw n))
      ((NetworkReady.machine n).initCfg input) = (ParserCountReady.machine n).initCfg input := rfl
  rw [hstart] at hreach
  have hlen := DecodedDimensions.copied_length_le input
  exact ⟨phase2Wrap (NetworkReady.machine n) (PrefixClear.machine (RoutedNetworkParser.raw n)) d,
    tc + 1 + td, by unfold ParserCountReady.timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt,
    hdcur, hdsafe, hdreg, hdkept, hdfree⟩

end JointThermoComplexity.Complexity.ParserCountReadyFree

#print axioms JointThermoComplexity.Complexity.ParserCountReadyFree.run
