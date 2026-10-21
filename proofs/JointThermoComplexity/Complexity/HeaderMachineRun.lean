module
public import proofs.JointThermoComplexity.Complexity.HeaderRewind

set_option autoImplicit false
@[expose] public section

/-! Header counting, canonical status and complete framed execution bounds. -/

namespace JointThermoComplexity.Complexity.HeaderMachineRun
open _root_.Complexity
open _root_.Complexity.TM
open HeaderMachine

variable {n : ℕ}

private theorem stop_rewind (k : ℕ) (valid : Bool) (word : List Bool)
    (c d : Cfg (n + 2) (machine n).Q) (hs : d.state = .rewind .moveLeft)
    (hc : c.work (counterIndex n) = growing k)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (hf : (c.work (flagIndex n)).head = 1)
    (hdw : d.work = NaturalMachine.flaggedWork c.work valid)
    (hi : d.input.read ≠ Γ.start) (hp : d.output.HasBinaryPrefix word) :
    ∃ e t, t ≤ k + 3 ∧ (machine n).reachesIn t d e ∧ (machine n).halted e ∧
      e.input = d.input ∧ e.output = d.output ∧
      (∀ i, i ≠ counterIndex n → i ≠ flagIndex n → e.work i = c.work i) ∧
      IsReg k (e.work (counterIndex n)) ∧ (e.work (flagIndex n)).head = 1 ∧
      (e.work (flagIndex n)).read = Γ.ofBool valid := by
  have hdc : d.work (counterIndex n) = growing k := by
    rw [hdw, NaturalMachine.flaggedWork_other c.work valid _ (counter_ne_flag n) (hw _).1, hc]
  have hfh : (d.work (flagIndex n)).head = 1 := by
    rw [hdw]
    exact NaturalMachine.flaggedWork_head c.work valid (hw _).1 hf
  have hfr : (d.work (flagIndex n)).read = Γ.ofBool valid := by
    rw [hdw]
    exact NaturalMachine.flaggedWork_read c.work valid (hw _).1 hf
  have hothers : ∀ i, i ≠ counterIndex n → (d.work i).read ≠ Γ.start ∧ 1 ≤ (d.work i).head := by
    intro i _
    by_cases heq : i = flagIndex n
    · subst i
      refine ⟨?_, by rw [hfh]⟩
      rw [hfr]
      cases valid <;> decide
    · rw [hdw, NaturalMachine.flaggedWork_other c.work valid i heq (hw i).1]
      exact hw i
  have ho : d.output.read ≠ Γ.start := by
    have hb : d.output.read = Γ.blank := by simp [Tape.read, hp.1, hp.2.2 word.length le_rfl]
    simp [hb]
  obtain ⟨e, t, ht, hreach, hhalt, hie, hoe, hwe, hreg⟩ :=
    HeaderRewind.run k d hs hdc hi ho (by rw [hp.1]; omega) hothers
  have hflag : e.work (flagIndex n) = d.work (flagIndex n) := hwe _ (counter_ne_flag n).symm
  refine ⟨e, t, ht, hreach, hhalt, hie, hoe, ?_, hreg, ?_, ?_⟩
  · intro i hcounter hflag'
    rw [hwe i hcounter, hdw, NaturalMachine.flaggedWork_other c.work valid i hflag' (hw i).1]
  · simpa only [hflag] using hfh
  · simpa only [hflag] using hfr

theorem scan (remaining : List Bool) :
    ∀ (k : ℕ) (before emitted : List Bool) (c : Cfg (n + 2) (machine n).Q),
      c.state = .count → c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells →
      c.input.head = before.length + 1 →
      (∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head) →
      c.work (counterIndex n) = growing k → (c.work (flagIndex n)).head = 1 →
      c.output.HasBinaryPrefix emitted → c.output.cells 0 = Γ.start →
      ∃ e t, t ≤ k + 2 * HeaderControl.count remaining + 4 ∧
        (machine n).reachesIn t c e ∧ (machine n).halted e ∧
        e.input.cells = c.input.cells ∧ e.input.head = before.length + (HeaderControl.copied remaining).length + 1 ∧
        (∀ i, i ≠ counterIndex n → i ≠ flagIndex n → e.work i = c.work i) ∧
        IsReg (k + HeaderControl.count remaining) (e.work (counterIndex n)) ∧
        (e.work (flagIndex n)).head = 1 ∧
        (e.work (flagIndex n)).read = Γ.ofBool (HeaderControl.valid remaining) ∧
        e.output.cells 0 = Γ.start ∧ e.output.HasBinaryPrefix (emitted ++ HeaderControl.copied remaining) := by
  induction remaining with
  | nil =>
    intro k before emitted c hs hcells hhead hw hc hf hp hz
    have hr : c.input.read = Γ.blank := by
      simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_ge before before.length le_rfl]
    have ho : c.output.read ≠ Γ.start := by
      have hb : c.output.read = Γ.blank := by simp [Tape.read, hp.1, hp.2.2 emitted.length le_rfl]
      simp [hb]
    let d : Cfg (n + 2) (machine n).Q := {
      state := .rewind .moveLeft, input := transitionInput c.input,
      work := NaturalMachine.flaggedWork c.work false, output := transitionTape c.output }
    have hstep : (machine n).step c = some d := eof_step c hs hr
    have hi : d.input = c.input := transitionInput_eq_self (by simp [hr])
    have hout : d.output = c.output := transitionTape_eq_self ho
    have hp' : d.output.HasBinaryPrefix emitted := by simpa only [hout] using hp
    obtain ⟨e, t, ht, hreach, hhalt, hie, hoe, hwe, hreg, hfh, hfr⟩ :=
      stop_rewind k false emitted c d rfl hc hw hf rfl (by simp [hi, hr]) hp'
    refine ⟨e, t + 1, ?_, ?_, hhalt, ?_, ?_, hwe, ?_, hfh, ?_, ?_, ?_⟩
    · simp only [HeaderControl.count]
      omega
    · simpa only [Nat.add_comm t 1] using TM.reachesIn.step hstep hreach
    · simp only [hie, hi]
    · simpa only [hie, hi, HeaderControl.copied, List.length_nil, Nat.add_zero] using hhead
    · simpa only [HeaderControl.count, Nat.add_zero] using hreg
    · exact hfr
    · simpa only [hoe, hout] using hz
    · simpa only [hoe, HeaderControl.copied, List.append_nil] using hp'
  | cons bit remaining ih =>
    intro k before emitted c hs hcells hhead hw hc hf hp hz
    have hindex : before.length < (before ++ bit :: remaining).length := by simp
    have hr : c.input.read = Γ.ofBool bit := by
      rw [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt _ before.length hindex]
      simp
    cases bit with
    | false =>
      let d : Cfg (n + 2) (machine n).Q := {
        state := .rewind .moveLeft, input := c.input.move .right,
        work := NaturalMachine.flaggedWork c.work true, output := c.output.writeAndMove Γ.zero .right }
      have hstep : (machine n).step c = some d := terminator_step c hs hr
      have hp' : d.output.HasBinaryPrefix (emitted ++ [false]) := Tape.hasBinaryPrefix_write_bit false hp
      have hz' : d.output.cells 0 = Γ.start := Tape.hasBinaryPrefix_write_bit_cell0 false hp hz
      have hri : d.input.read ≠ Γ.start := by
        simp only [d, Tape.read, Tape.move, hhead, hcells]
        exact Tape.init_ofBool_cells_ne_start _ _ (by omega)
      obtain ⟨e, t, ht, hreach, hhalt, hie, hoe, hwe, hreg, hfh, hfr⟩ :=
        stop_rewind k true (emitted ++ [false]) c d rfl hc hw hf rfl hri hp'
      refine ⟨e, t + 1, ?_, ?_, hhalt, ?_, ?_, hwe, ?_, hfh, ?_, ?_, ?_⟩
      · simp only [HeaderControl.count]
        omega
      · simpa only [Nat.add_comm t 1] using TM.reachesIn.step hstep hreach
      · simp [hie, d, Tape.move]
      · simp [hie, d, Tape.move, hhead, HeaderControl.copied]
      · simpa only [HeaderControl.count, Nat.add_zero] using hreg
      · exact hfr
      · simpa only [hoe] using hz'
      · simpa only [hoe, HeaderControl.copied] using hp'
    | true =>
      let d : Cfg (n + 2) (machine n).Q := {
        state := .count, input := c.input.move .right,
        work := pushedWork c.work, output := c.output.writeAndMove Γ.one .right }
      have hstep : (machine n).step c = some d := count_step c hs hr
      have hdc : d.work (counterIndex n) = growing (k + 1) := by
        simp only [d, pushedWork, ↓reduceIte, hc, growing_push]
      have hother (i : Fin (n + 2)) (hi : i ≠ counterIndex n) : d.work i = c.work i := by
        change pushedWork c.work i = c.work i
        rw [pushedWork, ite_eq_right hi]
        exact transitionTape_eq_self (hw i).1
      have hwd : ∀ i, (d.work i).read ≠ Γ.start ∧ 1 ≤ (d.work i).head := by
        intro i
        by_cases heq : i = counterIndex n
        · subst i
          rw [hdc]
          constructor
          · simp [growing_read]
          · simp [growing]
        · rw [hother i heq]
          exact hw i
      have hfd : (d.work (flagIndex n)).head = 1 := by rw [hother _ (counter_ne_flag n).symm]; exact hf
      have hpd : d.output.HasBinaryPrefix (emitted ++ [true]) := Tape.hasBinaryPrefix_write_bit true hp
      have hzd : d.output.cells 0 = Γ.start := Tape.hasBinaryPrefix_write_bit_cell0 true hp hz
      have hcd : d.input.cells = (Tape.init (((before ++ [true]) ++ remaining).map Γ.ofBool)).cells := by
        simpa [d, Tape.move, List.append_assoc] using hcells
      have hhd : d.input.head = (before ++ [true]).length + 1 := by
        simp [d, Tape.move, hhead, Nat.add_assoc]
      obtain ⟨e, t, ht, hreach, hhalt, hie, hhe, hwe, hreg, hfh, hfr, hze, hpe⟩ :=
        ih (k + 1) (before ++ [true]) (emitted ++ [true]) d rfl hcd hhd hwd hdc hfd hpd hzd
      refine ⟨e, t + 1, ?_, ?_, hhalt, ?_, ?_, ?_, ?_, hfh, ?_, hze, ?_⟩
      · simp only [HeaderControl.count]
        omega
      · simpa only [Nat.add_comm t 1] using TM.reachesIn.step hstep hreach
      · simpa only [d, Tape.move_cells] using hie
      · simp only [List.length_append, List.length_singleton] at hhe
        simp only [HeaderControl.copied, List.length_cons]
        omega
      · intro i hcounter hflag
        exact (hwe i hcounter hflag).trans (hother i hcounter)
      · have heq : k + 1 + HeaderControl.count remaining = k + HeaderControl.count (true :: remaining) := by
          simp [HeaderControl.count, Nat.add_comm, Nat.add_assoc]
        simpa only [heq] using hreg
      · exact hfr
      · simpa only [HeaderControl.copied, List.append_assoc, List.singleton_append] using hpe

theorem run_count_bound (before emitted remaining : List Bool)
    (c : Cfg (n + 2) (machine n).Q) (hs : c.state = .start)
    (hcells : c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells)
    (hhead : c.input.head = before.length + 1)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (hc : IsReg 0 (c.work (counterIndex n))) (hf : (c.work (flagIndex n)).head = 1)
    (hp : c.output.HasBinaryPrefix emitted) (hz : c.output.cells 0 = Γ.start) :
    ∃ e t, t ≤ 2 * HeaderControl.count remaining + 5 ∧ (machine n).reachesIn t c e ∧ (machine n).halted e ∧
      e.input.cells = c.input.cells ∧ e.input.head = before.length + (HeaderControl.copied remaining).length + 1 ∧
      (∀ i, i ≠ counterIndex n → i ≠ flagIndex n → e.work i = c.work i) ∧
      IsReg (HeaderControl.count remaining) (e.work (counterIndex n)) ∧
      (e.work (flagIndex n)).head = 1 ∧
      (e.work (flagIndex n)).read = Γ.ofBool (HeaderControl.valid remaining) ∧
      e.output.cells 0 = Γ.start ∧ e.output.HasBinaryPrefix (emitted ++ HeaderControl.copied remaining) := by
  have hi : c.input.read ≠ Γ.start := by
    rw [Tape.read, hhead, hcells]
    exact Tape.init_ofBool_cells_ne_start _ _ (by omega)
  have ho : c.output.read ≠ Γ.start := by
    have hb : c.output.read = Γ.blank := by simp [Tape.read, hp.1, hp.2.2 emitted.length le_rfl]
    simp [hb]
  let d : Cfg (n + 2) (machine n).Q := {
    state := .count, input := transitionInput c.input,
    work := fun i => transitionTape (c.work i), output := transitionTape c.output }
  have hstep : (machine n).step c = some d := by
    simp [TM.step, machine, action, hs, d, allReadBack, transitionInput, transitionTape]
  have hdi : d.input = c.input := transitionInput_eq_self hi
  have hdo : d.output = c.output := transitionTape_eq_self ho
  have hdw : d.work = c.work := by funext i; exact transitionTape_eq_self (hw i).1
  have hdg : d.work (counterIndex n) = growing 0 := by
    rw [hdw, hc.eq_regT]
    rfl
  obtain ⟨e, t, ht, hreach, hhalt, hie, hhe, hwe, hreg, hfh, hfr, hze, hpe⟩ :=
    scan remaining 0 before emitted d rfl (by simpa only [hdi] using hcells)
      (by simpa only [hdi] using hhead) (by rw [hdw]; exact hw) hdg
      (by rw [hdw]; exact hf) (by simpa only [hdo] using hp) (by simpa only [hdo] using hz)
  refine ⟨e, t + 1, ?_, ?_, hhalt, ?_, hhe, ?_, ?_, hfh, hfr, hze, hpe⟩
  · omega
  · simpa only [Nat.add_comm t 1] using TM.reachesIn.step hstep hreach
  · simpa only [hdi] using hie
  · intro i hcounter hflag
    exact (hwe i hcounter hflag).trans (congrFun hdw i)
  · simpa only [Nat.zero_add] using hreg

theorem run_from_cursor (before emitted remaining : List Bool)
    (c : Cfg (n + 2) (machine n).Q) (hs : c.state = .start)
    (hcells : c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells)
    (hhead : c.input.head = before.length + 1)
    (hw : ∀ i, (c.work i).read ≠ Γ.start ∧ 1 ≤ (c.work i).head)
    (hc : IsReg 0 (c.work (counterIndex n))) (hf : (c.work (flagIndex n)).head = 1)
    (hp : c.output.HasBinaryPrefix emitted) (hz : c.output.cells 0 = Γ.start) :
    ∃ e t, t ≤ 2 * remaining.length + 5 ∧ (machine n).reachesIn t c e ∧ (machine n).halted e ∧
      e.input.cells = c.input.cells ∧ e.input.head = before.length + (HeaderControl.copied remaining).length + 1 ∧
      (∀ i, i ≠ counterIndex n → i ≠ flagIndex n → e.work i = c.work i) ∧
      IsReg (HeaderControl.count remaining) (e.work (counterIndex n)) ∧
      (e.work (flagIndex n)).head = 1 ∧
      (e.work (flagIndex n)).read = Γ.ofBool (HeaderControl.valid remaining) ∧
      e.output.cells 0 = Γ.start ∧ e.output.HasBinaryPrefix (emitted ++ HeaderControl.copied remaining) := by
  obtain ⟨e, t, ht, hrest⟩ := run_count_bound before emitted remaining c hs hcells hhead hw hc hf hp hz
  have hn := HeaderControl.count_le_length remaining
  exact ⟨e, t, by omega, hrest⟩

end JointThermoComplexity.Complexity.HeaderMachineRun

#print axioms JointThermoComplexity.Complexity.HeaderMachineRun.run_from_cursor
#print axioms JointThermoComplexity.Complexity.HeaderMachineRun.run_count_bound
