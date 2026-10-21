module
public import proofs.JointThermoComplexity.Complexity.NetworkParser
public import proofs.JointThermoComplexity.Complexity.NetworkBodyFrame

set_option autoImplicit false
@[expose] public section

/-! The existing fresh parser leaves its reserved scratch bank exactly blank. -/

namespace JointThermoComplexity.Complexity.NetworkParserFree
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt NetworkParser

def port (n : ℕ) (i : Fin n) : Fin (n + 5) := i.castAdd 5

def Free (n : ℕ) (work : Fin (n + 5) → Tape) : Prop :=
  ∀ i : Fin n, work (port n i) = DimensionEntry.blankRegister

theorem port_ne_master (n : ℕ) (i : Fin n) : port n i ≠ master n := by
  intro h
  have hv := congrArg Fin.val h
  simp only [port, master, Fin.val_castAdd, Fin.val_last] at hv
  omega

theorem port_ne_flag (n : ℕ) (i : Fin n) : port n i ≠ flag n := by
  intro h
  have hv := congrArg Fin.val h
  simp only [port, NetworkParser.flag, NaturalMachine.flagIndex, Fin.val_castAdd, Fin.val_last] at hv
  omega

theorem run (n : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine n).reachesIn t ((machine n).initCfg input) d ∧
      (machine n).halted d ∧
      Cursor (NetworkInputControl.copied input) (NetworkInputControl.rest input) (NetworkInputControl.copied input)
        d.input d.work d.output ∧ (d.work (master n)).head = 1 ∧
      (d.work (master n)).read = Γ.ofBool (NetworkInputControl.accepted input) ∧
      NetworkScanner.Env (count n 0) (count n 1) (count n 2)
        (DimensionHeaders.species input) (DimensionHeaders.reactions input) (DimensionHeaders.cores input) d.work ∧ Free n d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hcur, hs, hr, hc, hf, hv, hfree⟩ := DimensionEntry.run (n + 1) input
  have hmhead : (c.work (master n)).head = 1 := by rw [master, hfree (Fin.last n)]; rfl
  have hFree : Free n c.work := fun i => hfree i.castSucc
  have hR : ∀ work work', (∀ j, j ≠ master n → j ≠ flag n → work' j = work j) → Free n work → Free n work' := by
    intro work work' hw h i
    exact (hw (port n i) (port_ne_master n i) (port_ne_flag n i)).trans (h i)
  have hbody := NetworkBodyFrame.hoareTime (count n 0) (count n 1) (count n 2) (master n)
    (count_ne_flag n 0) (count_ne_flag n 1) (count_ne_flag n 2) (master_ne_flag n)
    (count_ne_master n 0) (count_ne_master n 1) (count_ne_master n 2)
    (count_ne_count n 0 1 (by decide)) (count_ne_count n 0 2 (by decide)) (count_ne_count n 1 2 (by decide))
    (DimensionHeaders.species input) (DimensionHeaders.reactions input) (DimensionHeaders.cores input)
    (DimensionHeaders.accepted input) (DimensionEntry.consumed input) (DimensionHeaders.tail₃ input) (DimensionEntry.consumed input)
    (Free n) hR
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, _, hdmh, hdmv, henv, hdFree⟩ :=
    hbody c.input c.work c.output ⟨hcur, hmhead, hf, hv, ⟨hs, hr, hc⟩, hFree⟩
  obtain ⟨hi, hw, ho⟩ := hcur.phase
  have hreach₂ : (body n).reachesIn td
      ⟨(body n).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    simpa only [hi, hw, ho, body] using hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (DimensionEntry.machine (n + 1)) (body n) hcreach hchalt hreach₂
  have hstart : phase1Wrap (DimensionEntry.machine (n + 1)) (body n)
      ((DimensionEntry.machine (n + 1)).initCfg input) = (machine n).initCfg input := rfl
  rw [hstart] at hreach
  have htime : tc + 1 + td ≤ timeBound input.length := by
    have hraw : tc + 1 + td ≤ 2 * input.length + 25 + recordTime input := by
      change td ≤ recordTime input + 6 at htd
      omega
    exact hraw.trans (recordTime_le input)
  refine ⟨phase2Wrap (DimensionEntry.machine (n + 1)) (body n) d, tc + 1 + td, htime, hreach,
    (phase2Wrap_halted_iff _ _ d).mpr hdhalt, ?_, hdmh, ?_, henv, hdFree⟩
  · simpa only [phase2Wrap, NetworkInputControl.copied, NetworkInputControl.rest, NetworkInputControl.records] using hdcur
  · simpa only [phase2Wrap, NetworkInputControl.accepted, NetworkInputControl.records,
      NetworkRecords.accepted, Bool.and_assoc] using hdmv

end JointThermoComplexity.Complexity.NetworkParserFree

#print axioms JointThermoComplexity.Complexity.NetworkParserFree.run
