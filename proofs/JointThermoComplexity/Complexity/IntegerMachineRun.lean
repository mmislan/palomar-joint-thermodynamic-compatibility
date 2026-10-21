module
public import proofs.JointThermoComplexity.Complexity.IntegerMachine

set_option autoImplicit false
@[expose] public section

/-! Signed-integer scanning in linear time, with exact canonical codec status. -/

namespace JointThermoComplexity.Complexity.IntegerMachineRun
open _root_.Complexity
open _root_.Complexity.TM
open IntegerMachine

variable {n : ℕ}

def copied : List Bool → List Bool
  | [] => []
  | sign :: rest => sign :: PayloadControl.copied .empty rest

theorem run_sign_from_cursor (before emitted remaining : List Bool)
    (c : Cfg (n + 1) (machine n).Q) (hs : c.state = .sign)
    (hcells : c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells)
    (hhead : c.input.head = before.length + 1)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start) (hflag : (c.work (NaturalMachine.flagIndex n)).head = 1)
    (hp : c.output.HasBinaryPrefix emitted) (hzero : c.output.cells 0 = Γ.start) :
    ∃ c' t, t ≤ remaining.length + 2 ∧ (machine n).reachesIn t c c' ∧ (machine n).halted c' ∧
      c'.input.cells = c.input.cells ∧ c'.input.head = before.length + (copied remaining).length + 1 ∧
      (∀ i, i ≠ NaturalMachine.flagIndex n → c'.work i = c.work i) ∧
      (c'.work (NaturalMachine.flagIndex n)).head = 1 ∧
      (c'.work (NaturalMachine.flagIndex n)).read = Γ.ofBool (NaturalMachineParser.integerAccepted remaining) ∧
      c'.output.cells 0 = Γ.start ∧ c'.output.HasBinaryPrefix (emitted ++ copied remaining) := by
  cases remaining with
  | nil =>
    have hr : c.input.read = Γ.blank := by
      simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_ge before before.length le_rfl]
    have ho : c.output.read ≠ Γ.start := by
      have hb : c.output.read = Γ.blank := by simp [Tape.read, hp.1, hp.2.2 emitted.length le_rfl]
      simp [hb]
    let c' : Cfg (n + 1) (machine n).Q := {
      state := .done, input := transitionInput c.input,
      work := NaturalMachine.flaggedWork c.work false, output := transitionTape c.output }
    have hstep : (machine n).step c = some c' := eof_step c hs hr
    have hi : c'.input = c.input := transitionInput_eq_self (by simp [hr])
    have hout : c'.output = c.output := transitionTape_eq_self ho
    refine ⟨c', 1, by simp, .step hstep .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hi]
    · simpa only [hi, copied, List.length_nil, Nat.add_zero] using hhead
    · intro i hne
      exact NaturalMachine.flaggedWork_other c.work false i hne (hwork i)
    · exact NaturalMachine.flaggedWork_head c.work false (hwork _) hflag
    · exact NaturalMachine.flaggedWork_read c.work false (hwork _) hflag
    · simpa only [hout] using hzero
    · simpa only [hout, copied, List.append_nil] using hp
  | cons sign rest =>
    have hindex : before.length < (before ++ sign :: rest).length := by simp
    have hr : c.input.read = Γ.ofBool sign := by
      rw [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt _ before.length hindex]
      simp
    let c₁ : Cfg (n + 1) (machine n).Q := {
      state := .body sign .start, input := c.input.move .right,
      work := fun i => transitionTape (c.work i),
      output := c.output.writeAndMove (Γ.ofBool sign) .right }
    have hstep : (machine n).step c = some c₁ := sign_step c sign hs hr
    have hw₁ : c₁.work = c.work := by
      funext i
      exact transitionTape_eq_self (hwork i)
    have hp₁ : c₁.output.HasBinaryPrefix (emitted ++ [sign]) := Tape.hasBinaryPrefix_write_bit sign hp
    have hz₁ : c₁.output.cells 0 = Γ.start := Tape.hasBinaryPrefix_write_bit_cell0 sign hp hzero
    let d₀ : Cfg (n + 1) (NaturalMachine.machine sign n).Q :=
      ⟨.start, c₁.input, c₁.work, c₁.output⟩
    have hwrap : wrap sign d₀ = c₁ := rfl
    have hc₁ : d₀.input.cells = (Tape.init (((before ++ [sign]) ++ rest).map Γ.ofBool)).cells := by
      simpa [d₀, c₁, Tape.move, List.append_assoc] using hcells
    have hh₁ : d₀.input.head = (before ++ [sign]).length + 1 := by
      simp [d₀, c₁, Tape.move, hhead, Nat.add_assoc]
    have hwork₁ : ∀ i, (d₀.work i).read ≠ Γ.start := by
      change ∀ i, (c₁.work i).read ≠ Γ.start
      rw [hw₁]
      exact hwork
    have hflag₁ : (d₀.work (NaturalMachine.flagIndex n)).head = 1 := by
      change (c₁.work (NaturalMachine.flagIndex n)).head = 1
      rw [hw₁]
      exact hflag
    obtain ⟨d', t, ht, hreach, hhalt, hc', hh', hw', hf', hv', hz', hp'⟩ :=
      NaturalMachineParser.run_parser_from_cursor sign (before ++ [sign]) (emitted ++ [sign]) rest
        d₀ rfl hc₁ hh₁ hwork₁ hflag₁ hp₁ hz₁
    have hbody : (machine n).reachesIn t c₁ (wrap sign d') := by
      rw [← hwrap]
      exact body_reaches sign hreach
    refine ⟨wrap sign d', t + 1, ?_, ?_, body_halted sign d' hhalt, ?_, ?_, ?_, hf', ?_, hz', ?_⟩
    · simp only [List.length_cons]
      omega
    · simpa only [Nat.add_comm t 1] using TM.reachesIn.step hstep hbody
    · simpa only [wrap, d₀, c₁, Tape.move_cells] using hc'
    · change d'.input.head = _
      simp only [List.length_append, List.length_singleton] at hh'
      simp only [copied, List.length_cons]
      omega
    · intro i hne
      exact (hw' i hne).trans (congrFun hw₁ i)
    · simpa only [wrap, NaturalMachineParser.integerAccepted] using hv'
    · simpa only [wrap, copied, List.append_assoc, List.singleton_append] using hp'

private theorem input_read_ne_start (before remaining : List Bool) (c : Cfg (n + 1) (machine n).Q)
    (hcells : c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells)
    (hhead : c.input.head = before.length + 1) : c.input.read ≠ Γ.start := by
  rw [Tape.read, hhead, hcells]
  exact Tape.init_ofBool_cells_ne_start _ _ (by omega)

theorem run_from_cursor (before emitted remaining : List Bool)
    (c : Cfg (n + 1) (machine n).Q) (hs : c.state = .start)
    (hcells : c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells)
    (hhead : c.input.head = before.length + 1)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start) (hflag : (c.work (NaturalMachine.flagIndex n)).head = 1)
    (hp : c.output.HasBinaryPrefix emitted) (hzero : c.output.cells 0 = Γ.start) :
    ∃ c' t, t ≤ remaining.length + 3 ∧ (machine n).reachesIn t c c' ∧ (machine n).halted c' ∧
      c'.input.cells = c.input.cells ∧ c'.input.head = before.length + (copied remaining).length + 1 ∧
      (∀ i, i ≠ NaturalMachine.flagIndex n → c'.work i = c.work i) ∧
      (c'.work (NaturalMachine.flagIndex n)).head = 1 ∧
      (c'.work (NaturalMachine.flagIndex n)).read = Γ.ofBool (NaturalMachineParser.integerAccepted remaining) ∧
      c'.output.cells 0 = Γ.start ∧ c'.output.HasBinaryPrefix (emitted ++ copied remaining) := by
  have hr := input_read_ne_start before remaining c hcells hhead
  have ho : c.output.read ≠ Γ.start := by
    have hb : c.output.read = Γ.blank := by simp [Tape.read, hp.1, hp.2.2 emitted.length le_rfl]
    simp [hb]
  let c₁ : Cfg (n + 1) (machine n).Q := {
    state := .sign, input := transitionInput c.input,
    work := fun i => transitionTape (c.work i), output := transitionTape c.output }
  have hstep : (machine n).step c = some c₁ := by
    simp [TM.step, machine, action, hs, c₁, allReadBack, transitionInput, transitionTape]
  have hi : c₁.input = c.input := transitionInput_eq_self hr
  have hout : c₁.output = c.output := transitionTape_eq_self ho
  have hw : c₁.work = c.work := by
    funext i
    exact transitionTape_eq_self (hwork i)
  obtain ⟨c', t, ht, hreach, hhalt, hc', hh', hw', hf', hv', hz', hp'⟩ :=
    run_sign_from_cursor before emitted remaining c₁ rfl
      (by simpa only [hi] using hcells) (by simpa only [hi] using hhead)
      (by rw [hw]; exact hwork) (by rw [hw]; exact hflag)
      (by simpa only [hout] using hp) (by simpa only [hout] using hzero)
  refine ⟨c', t + 1, ?_, ?_, hhalt, ?_, hh', ?_, hf', hv', hz', hp'⟩
  · omega
  · simpa only [Nat.add_comm t 1] using TM.reachesIn.step hstep hreach
  · simpa only [hi] using hc'
  · intro i hne
    exact (hw' i hne).trans (congrFun hw i)

theorem codec_status_iff (input : List Bool) {value : Γ}
    (h : value = Γ.ofBool (NaturalMachineParser.integerAccepted input)) :
    value = Γ.one ↔ ∃ z suffix, BitCodec.parseInteger input = some (z, suffix) := by
  rw [h, ← NaturalMachineParser.integerAccepted_iff]
  cases NaturalMachineParser.integerAccepted input <;> simp [Γ.ofBool]

end JointThermoComplexity.Complexity.IntegerMachineRun

#print axioms JointThermoComplexity.Complexity.IntegerMachineRun.run_from_cursor
#print axioms JointThermoComplexity.Complexity.IntegerMachineRun.codec_status_iff
