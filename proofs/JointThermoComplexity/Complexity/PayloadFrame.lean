module
public import proofs.JointThermoComplexity.Complexity.PayloadMachine

set_option autoImplicit false
@[expose] public section

/-!
# Composable payload scanning with arbitrary working tapes

The input prefix and output accumulator are independent. Scanning preserves
input cells and every off-marker work tape, advances the input cursor by exactly
the copied prefix length, and preserves the output's left marker. The copied
payload is never interpreted as a unary number. The prior zero-work-tape scanner
and its successful receipt remain unchanged.
-/

namespace JointThermoComplexity.Complexity.PayloadFrame
open _root_.Complexity
open _root_.Complexity.TM
open PayloadMachine

def machine (n : ℕ) : TM n where
  Q := Phase
  qstart := .start
  qhalt := .done
  δ state iHead wHeads oHead :=
    let copyTo (p : Phase) :
        Phase × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3 :=
      (p, (fun i => readBackWrite (wHeads i)), readBackWrite iHead, Dir3.right,
        (fun i => idleDir (wHeads i)), Dir3.right)
    match state with
    | .start => allReadBack .flag iHead wHeads oHead
    | .done => allReadBack .done iHead wHeads oHead
    | .flag =>
      match iHead with
      | .zero => copyTo .done
      | .one => copyTo .payload
      | _ => allReadBack .done iHead wHeads oHead
    | .payload =>
      match iHead with
      | .zero | .one => copyTo .flag
      | _ => allReadBack .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state <;> cases iHead <;> simp [allReadBack, idleDir]

variable {n : ℕ}

private theorem copy_step (c : Cfg n (machine n).Q) (expect bit : Bool)
    (hs : c.state = phase expect) (hr : c.input.read = Γ.ofBool bit) :
    (machine n).step c = some {
      state := next expect bit
      input := c.input.move .right
      work := fun i => transitionTape (c.work i)
      output := c.output.writeAndMove (Γ.ofBool bit) .right } := by
  cases expect <;> cases bit <;>
    simp [TM.step, hs, phase, machine, hr, Γ.ofBool, next, readBackWrite, Γw.toΓ,
      transitionTape]

theorem scan (remaining : List Bool) :
    ∀ (before emitted : List Bool) (expect : Bool) (c : Cfg n (machine n).Q),
      c.state = phase expect →
      c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells →
      c.input.head = before.length + 1 →
      (∀ i, (c.work i).read ≠ Γ.start) →
      c.output.HasBinaryPrefix emitted → c.output.cells 0 = Γ.start →
      ∃ c' t, t ≤ (prefixFrom expect remaining).length + 1 ∧
        (machine n).reachesIn t c c' ∧ (machine n).halted c' ∧
        c'.input.cells = c.input.cells ∧
        c'.input.head = before.length + (prefixFrom expect remaining).length + 1 ∧
        c'.work = c.work ∧ c'.output.cells 0 = Γ.start ∧
        c'.output.HasBinaryPrefix (emitted ++ prefixFrom expect remaining) := by
  induction remaining with
  | nil =>
    intro before emitted expect c hs hcells hhead hwork hp hzero
    have hr : c.input.read = Γ.blank := by
      simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_ge before before.length le_rfl]
    have ho : c.output.read = Γ.blank := by
      simp [Tape.read, hp.1, hp.2.2 emitted.length le_rfl]
    let c' : Cfg n (machine n).Q := {
      state := .done
      input := transitionInput c.input
      work := fun i => transitionTape (c.work i)
      output := transitionTape c.output }
    have hstep : (machine n).step c = some c' := by
      cases expect <;>
        simp [TM.step, hs, phase, machine, hr, c', allReadBack, transitionInput, transitionTape]
    have hi : c'.input = c.input := by exact transitionInput_eq_self (by simp [hr])
    have hout : c'.output = c.output := by exact transitionTape_eq_self (by simp [ho])
    have hw : c'.work = c.work := by
      funext i
      exact transitionTape_eq_self (hwork i)
    refine ⟨c', 1, by simp [prefixFrom], .step hstep .zero, rfl, ?_, ?_, hw, ?_, ?_⟩
    · simp only [hi]
    · simpa only [hi, prefixFrom, List.length_nil, Nat.add_zero] using hhead
    · simpa only [hout] using hzero
    · simpa only [hout, prefixFrom, List.append_nil] using hp
  | cons b remaining ih =>
    intro before emitted expect c hs hcells hhead hwork hp hzero
    have hindex : before.length < (before ++ b :: remaining).length := by simp
    have hr : c.input.read = Γ.ofBool b := by
      rw [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt _ before.length hindex]
      simp
    let c₁ : Cfg n (machine n).Q := {
      state := next expect b
      input := c.input.move .right
      work := fun i => transitionTape (c.work i)
      output := c.output.writeAndMove (Γ.ofBool b) .right }
    have hstep : (machine n).step c = some c₁ := copy_step c expect b hs hr
    have hw₁ : c₁.work = c.work := by
      funext i
      exact transitionTape_eq_self (hwork i)
    have hp₁ : c₁.output.HasBinaryPrefix (emitted ++ [b]) := Tape.hasBinaryPrefix_write_bit b hp
    have hz₁ : c₁.output.cells 0 = Γ.start := Tape.hasBinaryPrefix_write_bit_cell0 b hp hzero
    by_cases stop : expect = false ∧ b = false
    · obtain ⟨rfl, rfl⟩ := stop
      refine ⟨c₁, 1, by simp [prefixFrom], .step hstep .zero, rfl, ?_, ?_, hw₁, hz₁, ?_⟩
      · simp [c₁, Tape.move]
      · simp [c₁, Tape.move, hhead, prefixFrom]
      · simpa only [prefixFrom] using hp₁
    · have hs₁ : c₁.state = phase (!expect) := by
        cases expect <;> cases b <;> simp_all [c₁, next, phase] <;> rfl
      have hc₁ : c₁.input.cells =
          (Tape.init (((before ++ [b]) ++ remaining).map Γ.ofBool)).cells := by
        simpa [c₁, Tape.move, List.append_assoc] using hcells
      have hh₁ : c₁.input.head = (before ++ [b]).length + 1 := by
        simp [c₁, Tape.move, hhead, Nat.add_assoc]
      have hwork₁ : ∀ i, (c₁.work i).read ≠ Γ.start := by rw [hw₁]; exact hwork
      obtain ⟨c', t, ht, hreach, hhalt, hcells', hhead', hwork', hzero', hp'⟩ :=
        ih (before ++ [b]) (emitted ++ [b]) (!expect) c₁ hs₁ hc₁ hh₁ hwork₁ hp₁ hz₁
      refine ⟨c', t + 1, ?_, ?_, hhalt, ?_, ?_, hwork'.trans hw₁, hzero', ?_⟩
      · cases expect <;> cases b <;> simp_all [prefixFrom]
      · simpa only [Nat.add_comm t 1] using TM.reachesIn.step hstep hreach
      · simpa only [c₁, Tape.move_cells] using hcells'
      · cases expect <;> cases b <;> simp_all [prefixFrom] <;> omega
      · cases expect <;> cases b <;> simp_all [prefixFrom, List.append_assoc]

private theorem input_read_ne_start (before remaining : List Bool) (c : Cfg n (machine n).Q)
    (hcells : c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells)
    (hhead : c.input.head = before.length + 1) : c.input.read ≠ Γ.start := by
  rw [Tape.read, hhead, hcells]
  by_cases h : before.length < (before ++ remaining).length
  · rw [Tape.init_ofBool_cells_lt _ before.length h]
    cases (before ++ remaining)[before.length] <;> decide
  · rw [Tape.init_ofBool_cells_ge _ before.length (by omega)]
    decide

theorem encoded_frame (before emitted payload suffix : List Bool) (c : Cfg n (machine n).Q)
    (hs : c.state = .start)
    (hcells : c.input.cells =
      (Tape.init ((before ++ (BitCodec.encodeBits payload ++ suffix)).map Γ.ofBool)).cells)
    (hhead : c.input.head = before.length + 1)
    (hwork : ∀ i, (c.work i).read ≠ Γ.start)
    (hp : c.output.HasBinaryPrefix emitted) (hzero : c.output.cells 0 = Γ.start) :
    ∃ c' t, t ≤ (BitCodec.encodeBits payload).length + 2 ∧
      (machine n).reachesIn t c c' ∧ (machine n).halted c' ∧
      c'.input.cells = c.input.cells ∧
      c'.input.head = before.length + (BitCodec.encodeBits payload).length + 1 ∧
      c'.work = c.work ∧ c'.output.cells 0 = Γ.start ∧
      c'.output.HasBinaryPrefix (emitted ++ BitCodec.encodeBits payload) := by
  have hr := input_read_ne_start before (BitCodec.encodeBits payload ++ suffix) c hcells hhead
  have ho : c.output.read ≠ Γ.start := by
    have hb : c.output.read = Γ.blank := by
      simp [Tape.read, hp.1, hp.2.2 emitted.length le_rfl]
    simp [hb]
  let c₁ : Cfg n (machine n).Q := {
    state := .flag
    input := transitionInput c.input
    work := fun i => transitionTape (c.work i)
    output := transitionTape c.output }
  have hstep : (machine n).step c = some c₁ := by
    simp [TM.step, hs, machine, c₁, allReadBack, transitionInput, transitionTape]
  have hi : c₁.input = c.input := transitionInput_eq_self hr
  have hout : c₁.output = c.output := transitionTape_eq_self ho
  have hw : c₁.work = c.work := by
    funext i
    exact transitionTape_eq_self (hwork i)
  have hpre : prefixFrom false (BitCodec.encodeBits payload ++ suffix) = BitCodec.encodeBits payload :=
    prefix_encoded payload suffix
  obtain ⟨c', t, ht, hreach, hhalt, hc', hh', hw', hz', hp'⟩ :=
    scan (BitCodec.encodeBits payload ++ suffix) before emitted false c₁ rfl
      (by simpa only [hi] using hcells) (by simpa only [hi] using hhead)
      (by rw [hw]; exact hwork) (by simpa only [hout] using hp)
      (by simpa only [hout] using hzero)
  refine ⟨c', t + 1, ?_, ?_, hhalt, ?_, ?_, hw'.trans hw, hz', ?_⟩
  · rw [hpre] at ht
    omega
  · simpa only [Nat.add_comm t 1] using TM.reachesIn.step hstep hreach
  · simpa only [hi] using hc'
  · simpa only [hpre] using hh'
  · simpa only [hpre] using hp'

end JointThermoComplexity.Complexity.PayloadFrame

#print axioms JointThermoComplexity.Complexity.PayloadFrame.scan
#print axioms JointThermoComplexity.Complexity.PayloadFrame.encoded_frame
