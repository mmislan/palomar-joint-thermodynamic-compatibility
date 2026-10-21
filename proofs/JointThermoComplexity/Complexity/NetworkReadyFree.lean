module
public import proofs.JointThermoComplexity.Complexity.RoutedParserFree
public import proofs.JointThermoComplexity.Complexity.NetworkReady

set_option autoImplicit false
@[expose] public section

/-! The existing formula-preparation machine preserves its reserved blank registers. -/

namespace JointThermoComplexity.Complexity.NetworkReadyFree
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem run (n : ℕ) (input : List Bool) :
    ∃ d t, t ≤ NetworkReady.timeBound input.length ∧
      (NetworkReady.machine n).reachesIn t ((NetworkReady.machine n).initCfg input) d ∧
      (NetworkReady.machine n).halted d ∧ Cursor [] input [] d.input d.work d.output ∧
      RoutedNetworkParser.Retained n input d.work ∧ NetworkParserFree.Free n (CountAppend.oldWork d.work) := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hret, hfree⟩ := RoutedParserFree.run n input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdret, hdfree⟩ :=
    InputRewind.hoareTime (NetworkInputControl.copied input) (NetworkInputControl.rest input) []
      (fun work => RoutedNetworkParser.Retained n input work ∧ NetworkParserFree.Free n (CountAppend.oldWork work))
      c.input c.work c.output ⟨hc, hret, hfree⟩
  obtain ⟨hi, hw, ho⟩ := hc.phase
  have hr : (rewindInputTM (n := n + 6)).reachesIn td
      ⟨(rewindInputTM (n := n + 6)).qstart, transitionInput c.input,
        (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, ho] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (RoutedNetworkParser.machine n) rewindInputTM hcreach hchalt hr
  have hstart : phase1Wrap (RoutedNetworkParser.machine n) rewindInputTM
      ((RoutedNetworkParser.machine n).initCfg input) = (NetworkReady.machine n).initCfg input := rfl
  rw [hstart] at hreach
  have hlen := congrArg List.length (NetworkInputControl.consumed_split input)
  simp only [List.length_append] at hlen
  exact ⟨phase2Wrap (RoutedNetworkParser.machine n) rewindInputTM d, tc + 1 + td,
    by unfold NetworkReady.timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt,
    by simpa only [phase2Wrap, NetworkInputControl.consumed_split] using hdcur, hdret, hdfree⟩

end JointThermoComplexity.Complexity.NetworkReadyFree

#print axioms JointThermoComplexity.Complexity.NetworkReadyFree.run
