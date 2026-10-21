module
public import proofs.JointThermoComplexity.Complexity.NetworkParserFree
public import proofs.JointThermoComplexity.Complexity.RoutedNetworkParser
public import proofs.JointThermoComplexity.Complexity.CountAppend

set_option autoImplicit false
@[expose] public section

/-! Route copied parser output while retaining the exact blank spare bank. -/

namespace JointThermoComplexity.Complexity.RoutedParserFree
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt RoutedNetworkParser

theorem run (n : ℕ) (input : List Bool) :
    ∃ d t, t ≤ NetworkParser.timeBound input.length ∧
      (machine n).reachesIn t ((machine n).initCfg input) d ∧ (machine n).halted d ∧
      Cursor (NetworkInputControl.copied input) (NetworkInputControl.rest input) [] d.input d.work d.output ∧
      Retained n input d.work ∧ NetworkParserFree.Free n (CountAppend.oldWork d.work) := by
  obtain ⟨d, t, ht, hreach, hhalt, hc, hmhead, hmread, henv, hfree⟩ := NetworkParserFree.run n input
  have htpos : 0 < t := by
    cases hreach with
    | zero =>
      change Sum.inl (DimensionEntry.machine (n + 1)).qstart = Sum.inr (NetworkParser.body n).qhalt at hhalt
      cases hhalt
    | step => omega
  let c := OutputRoute.cfg (NetworkParser.machine n) ((Tape.init []).move Dir3.right) d
  have hr := OutputRouteEntry.init_reaches (NetworkParser.machine n) input hreach htpos
  have hcur : Cursor (NetworkInputControl.copied input) (NetworkInputControl.rest input) [] c.input c.work c.output := by
    refine ⟨hc.cells, hc.head, ?_, Tape.init_nil_move_right_hasBinaryPrefix_nil, ?_⟩
    · intro j
      by_cases hj : j.val < n + 5
      · let k : Fin (n + 5) := ⟨j.val, hj⟩
        have he : j = k.castSucc := rfl
        change ((OutputRoute.cfg (NetworkParser.machine n) ((Tape.init []).move Dir3.right) d).work j).read ≠ Γ.start ∧ _
        rw [he, OutputRoute.cfg_work]
        exact hc.works k
      · have he : j = Fin.last (n + 5) := by apply Fin.ext; simp only [Fin.val_last]; omega
        change ((OutputRoute.cfg (NetworkParser.machine n) ((Tape.init []).move Dir3.right) d).work j).read ≠ Γ.start ∧ _
        rw [he, OutputRoute.cfg_last]
        exact ⟨by rw [hc.tapePrefix.read_blank]; simp, by rw [hc.tapePrefix.1]; omega⟩
    · simp [c, OutputRoute.cfg, Tape.move, Tape.init]
  refine ⟨c, t, ht, hr, hhalt, hcur, ?_, ?_⟩
  · change Retained n input (OutputRoute.cfg (NetworkParser.machine n) ((Tape.init []).move Dir3.right) d).work
    unfold Retained raw master count
    simp only [OutputRoute.cfg_work, OutputRoute.cfg_last]
    exact ⟨hc.tapePrefix, hc.zero, hmhead, hmread, by
      simpa only [NetworkScanner.Env, OutputRoute.cfg_work] using henv⟩
  · intro i
    change (OutputRoute.cfg (NetworkParser.machine n) ((Tape.init []).move Dir3.right) d).work
      (NetworkParserFree.port n i).castSucc = DimensionEntry.blankRegister
    rw [OutputRoute.cfg_work]
    exact hfree i

end JointThermoComplexity.Complexity.RoutedParserFree

#print axioms JointThermoComplexity.Complexity.RoutedParserFree.run
