module
public import proofs.JointThermoComplexity.Complexity.BitCodec
public import proofs.Complexitylib.Models.TuringMachine.Subroutines.CopyOutput

set_option autoImplicit false
@[expose] public section

/-!
# A binary-machine scanner for self-delimiting payloads

The concrete machine copies one encoded payload prefix without expanding the
represented natural number. It halts on every binary input, including truncated
data. The simulation pattern uses the preserved Apache-2.0 Complexitylib tape
lemmas and its input-to-output copy proof; see third_party/complexitylib/LICENSE.
-/

namespace JointThermoComplexity.Complexity.PayloadMachine
open _root_.Complexity
open _root_.Complexity.TM

def prefixFrom : Bool → List Bool → List Bool
  | _, [] => []
  | true, b :: rest => b :: prefixFrom false rest
  | false, false :: _ => [false]
  | false, true :: rest => true :: prefixFrom true rest

def payloadPrefix (input : List Bool) : List Bool := prefixFrom false input

theorem prefix_encoded (payload suffix : List Bool) :
    payloadPrefix (BitCodec.encodeBits payload ++ suffix) = BitCodec.encodeBits payload := by
  induction payload with
  | nil => rfl
  | cons b bits ih =>
    simpa only [payloadPrefix, BitCodec.encodeBits, List.cons_append, prefixFrom] using
      congrArg (fun xs => true :: b :: xs) ih

inductive Phase where
  | start | flag | payload | done
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.start, .flag, .payload, .done}
  complete p := by cases p <;> simp

def phase (expectPayload : Bool) : Phase := if expectPayload then .payload else .flag

def next (expectPayload bit : Bool) : Phase :=
  if expectPayload then .flag else if bit then .payload else .done

def machine : TM 0 where
  Q := Phase
  qstart := .start
  qhalt := .done
  δ state iHead wHeads oHead :=
    let copyTo (p : Phase) :
        Phase × (Fin 0 → Γw) × Γw × Dir3 × (Fin 0 → Dir3) × Dir3 :=
      (p, (fun _ => Γw.blank), readBackWrite iHead, Dir3.right,
        (fun i => idleDir (wHeads i)), Dir3.right)
    match state with
    | .start => allIdle .flag iHead wHeads oHead
    | .done => allIdle .done iHead wHeads oHead
    | .flag =>
      match iHead with
      | .zero => copyTo .done
      | .one => copyTo .payload
      | _ => allIdle .done iHead wHeads oHead
    | .payload =>
      match iHead with
      | .zero | .one => copyTo .flag
      | _ => allIdle .done iHead wHeads oHead
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state <;> cases iHead <;>
      simp [allIdle, idleDir]

theorem empty_work (f : Fin 0 → Tape) : f = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

private theorem copy_step (c : Cfg 0 machine.Q) (expect bit : Bool)
    (hs : c.state = phase expect) (hr : c.input.read = Γ.ofBool bit) :
    machine.step c = some {
      state := next expect bit
      input := c.input.move .right
      work := Fin.elim0
      output := c.output.writeAndMove (Γ.ofBool bit) .right } := by
  cases expect <;> cases bit <;>
    simp [TM.step, hs, phase, machine, hr, Γ.ofBool, next, readBackWrite, Γw.toΓ, funext_iff]

private theorem scan (remaining : List Bool) :
    ∀ (processed : List Bool) (expect : Bool) (c : Cfg 0 machine.Q),
      c.state = phase expect →
      c.input.cells = (Tape.init ((processed ++ remaining).map Γ.ofBool)).cells →
      c.input.head = processed.length + 1 →
      c.output.HasBinaryPrefix processed →
      ∃ c' t, t ≤ remaining.length + 1 ∧ machine.reachesIn t c c' ∧ machine.halted c' ∧
        c'.output.HasBinaryPrefix (processed ++ prefixFrom expect remaining) := by
  induction remaining with
  | nil =>
    intro processed expect c hs hcells hhead hp
    have hr : c.input.read = Γ.blank := by
      simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_ge processed processed.length le_rfl]
    have ho : c.output.read = Γ.blank := by
      simp [Tape.read, hp.1, hp.2.2 processed.length le_rfl]
    have hkeep : c.output.writeAndMove Γ.blank Dir3.stay = c.output := by
      have hk := transitionTape_eq_self (t := c.output) (by simp [ho])
      simpa [transitionTape, ho, readBackWrite, idleDir] using hk
    let c' : Cfg 0 machine.Q := {
      state := .done, input := c.input, work := Fin.elim0, output := c.output }
    have hstep : machine.step c = some c' := by
      cases expect <;>
        simp [TM.step, hs, phase, machine, hr, c', allIdle, idleDir, ho,
          hkeep, Tape.move, funext_iff]
    exact ⟨c', 1, by simp, .step hstep .zero, rfl, by simpa [c', prefixFrom] using hp⟩
  | cons b remaining ih =>
    intro processed expect c hs hcells hhead hp
    have hindex : processed.length < (processed ++ b :: remaining).length := by simp
    have hr : c.input.read = Γ.ofBool b := by
      rw [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt _ processed.length hindex]
      simp
    let c₁ : Cfg 0 machine.Q := {
      state := next expect b
      input := c.input.move .right
      work := Fin.elim0
      output := c.output.writeAndMove (Γ.ofBool b) .right }
    have hstep : machine.step c = some c₁ := copy_step c expect b hs hr
    have hp₁ : c₁.output.HasBinaryPrefix (processed ++ [b]) := Tape.hasBinaryPrefix_write_bit b hp
    by_cases stop : expect = false ∧ b = false
    · obtain ⟨rfl, rfl⟩ := stop
      exact ⟨c₁, 1, by simp, .step hstep .zero, rfl, by simpa [prefixFrom] using hp₁⟩
    · have hs₁ : c₁.state = phase (!expect) := by
        cases expect <;> cases b <;> simp_all [c₁, next, phase] <;> rfl
      have hc₁ : c₁.input.cells =
          (Tape.init (((processed ++ [b]) ++ remaining).map Γ.ofBool)).cells := by
        simpa [c₁, Tape.move, List.append_assoc] using hcells
      have hh₁ : c₁.input.head = (processed ++ [b]).length + 1 := by
        simp [c₁, Tape.move, hhead, Nat.add_assoc]
      obtain ⟨c', t, ht, hreach, hhalt, hp'⟩ := ih (processed ++ [b]) (!expect) c₁ hs₁ hc₁ hh₁ hp₁
      refine ⟨c', t + 1, by simp only [List.length_cons]; omega, ?_, hhalt, ?_⟩
      · simpa only [Nat.add_comm t 1] using TM.reachesIn.step hstep hreach
      · cases expect <;> cases b <;> simp_all [prefixFrom, List.append_assoc]

theorem computesInTime : machine.ComputesInTime payloadPrefix (fun L => L + 2) := by
  intro input
  let c₁ : Cfg 0 machine.Q := {
    state := .flag
    input := (Tape.init (input.map Γ.ofBool)).move .right
    work := Fin.elim0
    output := (Tape.init []).move .right }
  have hstep : machine.step (machine.initCfg input) = some c₁ := by
    simp [TM.step, machine, c₁, allIdle, idleDir, Tape.read, Tape.init,
      Tape.writeAndMove, Tape.write, Tape.move, funext_iff]
  obtain ⟨c', t, ht, hreach, hhalt, hp⟩ := scan input [] false c₁ rfl
    (by simp [c₁, Tape.move]) (by simp [c₁, Tape.move])
    (by simpa only [c₁] using Tape.init_nil_move_right_hasBinaryPrefix_nil)
  refine ⟨c', t + 1, by change t + 1 ≤ input.length + 2; omega, ?_, hhalt, ?_⟩
  · simpa only [Nat.add_comm t 1] using TM.reachesIn.step hstep hreach
  · have hp' : c'.output.HasBinaryPrefix (payloadPrefix input) := by simpa [payloadPrefix] using hp
    exact ⟨hp'.2.1, hp'.2.2 _ (Nat.le_refl _)⟩

end JointThermoComplexity.Complexity.PayloadMachine

#print axioms JointThermoComplexity.Complexity.PayloadMachine.prefix_encoded
#print axioms JointThermoComplexity.Complexity.PayloadMachine.computesInTime
