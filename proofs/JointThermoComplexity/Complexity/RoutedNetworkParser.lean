module
public import proofs.JointThermoComplexity.Complexity.OutputRouteEntry
public import proofs.JointThermoComplexity.Complexity.NetworkParser

set_option autoImplicit false
@[expose] public section

/-! Fresh canonical parsing retains its verdict while routing copied input to work. -/

namespace JointThermoComplexity.Complexity.RoutedNetworkParser
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def machine (n : ℕ) : TM (n + 6) := (NetworkParser.machine n).retargetOutput
def count (n : ℕ) (j : Fin 3) : Fin (n + 6) := (NetworkParser.count n j).castSucc
def master (n : ℕ) : Fin (n + 6) := (NetworkParser.master n).castSucc
def raw (n : ℕ) : Fin (n + 6) := Fin.last (n + 5)

def Retained (n : ℕ) (input : List Bool) (work : Fin (n + 6) → Tape) : Prop :=
  (work (raw n)).HasBinaryPrefix (NetworkInputControl.copied input) ∧
  (work (raw n)).cells 0 = Γ.start ∧
  (work (master n)).head = 1 ∧
  (work (master n)).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
  NetworkScanner.Env (count n 0) (count n 1) (count n 2)
    (DimensionHeaders.species input) (DimensionHeaders.reactions input) (DimensionHeaders.cores input) work

theorem run (n : ℕ) (input : List Bool) :
    ∃ d t, t ≤ NetworkParser.timeBound input.length ∧
      (machine n).reachesIn t ((machine n).initCfg input) d ∧ (machine n).halted d ∧
      Cursor (NetworkInputControl.copied input) (NetworkInputControl.rest input) [] d.input d.work d.output ∧
      Retained n input d.work := by
  obtain ⟨d, t, ht, hreach, hhalt, hc, hmhead, hmread, henv⟩ := NetworkParser.run n input
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
  refine ⟨c, t, ht, hr, hhalt, hcur, ?_⟩
  change Retained n input (OutputRoute.cfg (NetworkParser.machine n) ((Tape.init []).move Dir3.right) d).work
  unfold Retained raw master count
  simp only [OutputRoute.cfg_work, OutputRoute.cfg_last]
  exact ⟨hc.tapePrefix, hc.zero, hmhead, hmread, by
    simpa only [NetworkScanner.Env, OutputRoute.cfg_work] using henv⟩

end JointThermoComplexity.Complexity.RoutedNetworkParser

#print axioms JointThermoComplexity.Complexity.RoutedNetworkParser.run
