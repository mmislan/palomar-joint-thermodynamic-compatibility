module
public import proofs.JointThermoComplexity.Complexity.NaturalMachine

set_option autoImplicit false
@[expose] public section

/-!
# Linear-time canonical validation with a composable frame

The simulation includes every binary input, malformed payloads and truncation.
The status flag agrees with the proved finite-control verdict. All other work
tapes and input cells are preserved, while the input cursor records exactly the
consumed structural prefix. Input and output prefixes remain independent.
-/

namespace JointThermoComplexity.Complexity.NaturalMachineRun
open _root_.Complexity
open _root_.Complexity.TM
open PayloadControl NaturalMachine

variable {n : ℕ}

theorem copied_length_le (p : ReadState) (input : List Bool) : (copied p input).length ≤ input.length := by
  induction input generalizing p with
  | nil => simp [copied]
  | cons b rest ih =>
    cases hn : next p b with
    | none => simp [copied, hn]
    | some q =>
      have ht := ih q
      simp only [copied, hn, List.length_cons]
      omega

theorem scan (requirePositive : Bool) (remaining : List Bool) :
    ∀ (before emitted : List Bool) (p : ReadState) (c : Cfg (n + 1) (machine requirePositive n).Q),
      c.state = .read p →
      c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells →
      c.input.head = before.length + 1 →
      (∀ i, (c.work i).read ≠ Γ.start) → (c.work (flagIndex n)).head = 1 →
      c.output.HasBinaryPrefix emitted → c.output.cells 0 = Γ.start →
      ∃ c' t, t ≤ (copied p remaining).length + 1 ∧
        (machine requirePositive n).reachesIn t c c' ∧ (machine requirePositive n).halted c' ∧
        c'.input.cells = c.input.cells ∧
        c'.input.head = before.length + (copied p remaining).length + 1 ∧
        (∀ i, i ≠ flagIndex n → c'.work i = c.work i) ∧
        (c'.work (flagIndex n)).head = 1 ∧
        (c'.work (flagIndex n)).read = Γ.ofBool (verdict requirePositive p remaining) ∧
        c'.output.cells 0 = Γ.start ∧ c'.output.HasBinaryPrefix (emitted ++ copied p remaining) := by
  induction remaining with
  | nil =>
    intro before emitted p c hs hcells hhead hwork hflag hp hzero
    have hr : c.input.read = Γ.blank := by
      simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_ge before before.length le_rfl]
    have ho : c.output.read ≠ Γ.start := by
      have hb : c.output.read = Γ.blank := by
        simp [Tape.read, hp.1, hp.2.2 emitted.length le_rfl]
      simp [hb]
    let c' : Cfg (n + 1) (machine requirePositive n).Q := {
      state := .done, input := transitionInput c.input,
      work := flaggedWork c.work false, output := transitionTape c.output }
    have hstep : (machine requirePositive n).step c = some c' := eof_step requirePositive c p hs hr
    have hi : c'.input = c.input := transitionInput_eq_self (by simp [hr])
    have hout : c'.output = c.output := transitionTape_eq_self ho
    refine ⟨c', 1, by simp [copied], .step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hi]
    · simpa only [hi, copied, List.length_nil, Nat.add_zero] using hhead
    · intro i hne
      exact flaggedWork_other c.work false i hne (hwork i)
    · exact flaggedWork_head c.work false (hwork _) hflag
    · exact flaggedWork_read c.work false (hwork _) hflag
    · simpa only [hout] using hzero
    · simpa only [hout, copied, List.append_nil] using hp
  | cons b remaining ih =>
    intro before emitted p c hs hcells hhead hwork hflag hp hzero
    have hindex : before.length < (before ++ b :: remaining).length := by simp
    have hr : c.input.read = Γ.ofBool b := by
      rw [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt _ before.length hindex]
      simp
    cases hnext : next p b with
    | none =>
      let c' : Cfg (n + 1) (machine requirePositive n).Q := {
        state := .done, input := c.input.move .right,
        work := flaggedWork c.work (accept requirePositive p),
        output := c.output.writeAndMove (Γ.ofBool b) .right }
      have hstep : (machine requirePositive n).step c = some c' :=
        finish_step requirePositive c p b hs hr hnext
      have hp' : c'.output.HasBinaryPrefix (emitted ++ [b]) := Tape.hasBinaryPrefix_write_bit b hp
      have hz' : c'.output.cells 0 = Γ.start := Tape.hasBinaryPrefix_write_bit_cell0 b hp hzero
      refine ⟨c', 1, by simp [copied, hnext], .step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_, hz', ?_⟩
      · simp [c', Tape.move]
      · simp [c', Tape.move, hhead, copied, hnext]
      · intro i hne
        exact flaggedWork_other c.work _ i hne (hwork i)
      · exact flaggedWork_head c.work _ (hwork _) hflag
      · simpa only [verdict, hnext] using flaggedWork_read c.work (accept requirePositive p) (hwork _) hflag
      · simpa only [copied, hnext] using hp'
    | some q =>
      let c₁ : Cfg (n + 1) (machine requirePositive n).Q := {
        state := .read q, input := c.input.move .right,
        work := fun i => transitionTape (c.work i),
        output := c.output.writeAndMove (Γ.ofBool b) .right }
      have hstep : (machine requirePositive n).step c = some c₁ :=
        continue_step requirePositive c p q b hs hr hnext
      have hw₁ : c₁.work = c.work := by
        funext i
        exact transitionTape_eq_self (hwork i)
      have hp₁ : c₁.output.HasBinaryPrefix (emitted ++ [b]) := Tape.hasBinaryPrefix_write_bit b hp
      have hz₁ : c₁.output.cells 0 = Γ.start := Tape.hasBinaryPrefix_write_bit_cell0 b hp hzero
      have hc₁ : c₁.input.cells =
          (Tape.init (((before ++ [b]) ++ remaining).map Γ.ofBool)).cells := by
        simpa [c₁, Tape.move, List.append_assoc] using hcells
      have hh₁ : c₁.input.head = (before ++ [b]).length + 1 := by
        simp [c₁, Tape.move, hhead, Nat.add_assoc]
      obtain ⟨c', t, ht, hreach, hhalt, hc', hh', hw', hf', hv', hz', hp'⟩ :=
        ih (before ++ [b]) (emitted ++ [b]) q c₁ rfl hc₁ hh₁
          (by rw [hw₁]; exact hwork) (by rw [hw₁]; exact hflag) hp₁ hz₁
      refine ⟨c', t + 1, ?_, ?_, hhalt, ?_, ?_, ?_, hf', ?_, hz', ?_⟩
      · simp only [copied, hnext, List.length_cons]
        omega
      · simpa only [Nat.add_comm t 1] using TM.reachesIn.step hstep hreach
      · simpa only [c₁, Tape.move_cells] using hc'
      · simp only [List.length_append, List.length_singleton] at hh'
        simp only [copied, hnext, List.length_cons]
        omega
      · intro i hne
        exact (hw' i hne).trans (congrFun hw₁ i)
      · simpa only [verdict, hnext] using hv'
      · simpa only [copied, hnext, List.append_assoc, List.singleton_append] using hp'

private theorem input_read_ne_start (before remaining : List Bool)
    (requirePositive : Bool) (c : Cfg (n + 1) (machine requirePositive n).Q)
    (hcells : c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells)
    (hhead : c.input.head = before.length + 1) : c.input.read ≠ Γ.start := by
  rw [Tape.read, hhead, hcells]
  by_cases h : before.length < (before ++ remaining).length
  · rw [Tape.init_ofBool_cells_lt _ before.length h]
    cases (before ++ remaining)[before.length] <;> decide
  · rw [Tape.init_ofBool_cells_ge _ before.length (by omega)]
    decide

theorem run_from_cursor (requirePositive : Bool) (before emitted remaining : List Bool)
    (c : Cfg (n + 1) (machine requirePositive n).Q) (hs : c.state = .start)
    (hcells : c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells)
    (hhead : c.input.head = before.length + 1)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start) (hflag : (c.work (flagIndex n)).head = 1)
    (hp : c.output.HasBinaryPrefix emitted) (hzero : c.output.cells 0 = Γ.start) :
    ∃ c' t, t ≤ remaining.length + 2 ∧
      (machine requirePositive n).reachesIn t c c' ∧ (machine requirePositive n).halted c' ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = before.length + (copied .empty remaining).length + 1 ∧
      (∀ i, i ≠ flagIndex n → c'.work i = c.work i) ∧
      (c'.work (flagIndex n)).head = 1 ∧
      (c'.work (flagIndex n)).read = Γ.ofBool (verdict requirePositive .empty remaining) ∧
      c'.output.cells 0 = Γ.start ∧ c'.output.HasBinaryPrefix (emitted ++ copied .empty remaining) := by
  have hr := input_read_ne_start before remaining requirePositive c hcells hhead
  have ho : c.output.read ≠ Γ.start := by
    have hb : c.output.read = Γ.blank := by
      simp [Tape.read, hp.1, hp.2.2 emitted.length le_rfl]
    simp [hb]
  let c₁ : Cfg (n + 1) (machine requirePositive n).Q := {
    state := .read .empty, input := transitionInput c.input,
    work := fun i => transitionTape (c.work i), output := transitionTape c.output }
  have hstep : (machine requirePositive n).step c = some c₁ := by
    simp [TM.step, machine, action, hs, c₁, allReadBack, transitionInput, transitionTape]
  have hi : c₁.input = c.input := transitionInput_eq_self hr
  have hout : c₁.output = c.output := transitionTape_eq_self ho
  have hw : c₁.work = c.work := by
    funext i
    exact transitionTape_eq_self (hwork i)
  obtain ⟨c', t, ht, hreach, hhalt, hc', hh', hw', hf', hv', hz', hp'⟩ :=
    scan requirePositive remaining before emitted .empty c₁ rfl
      (by simpa only [hi] using hcells) (by simpa only [hi] using hhead)
      (by rw [hw]; exact hwork) (by rw [hw]; exact hflag)
      (by simpa only [hout] using hp) (by simpa only [hout] using hzero)
  refine ⟨c', t + 1, ?_, ?_, hhalt, ?_, hh', ?_, hf', hv', hz', hp'⟩
  · have hl := copied_length_le .empty remaining
    omega
  · simpa only [Nat.add_comm t 1] using TM.reachesIn.step hstep hreach
  · simpa only [hi] using hc'
  · intro i hne
    exact (hw' i hne).trans (congrFun hw i)

end JointThermoComplexity.Complexity.NaturalMachineRun

#print axioms JointThermoComplexity.Complexity.NaturalMachineRun.scan
#print axioms JointThermoComplexity.Complexity.NaturalMachineRun.run_from_cursor
