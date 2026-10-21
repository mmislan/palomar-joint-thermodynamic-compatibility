module
public import proofs.JointThermoComplexity.Complexity.NaturalMachine

set_option autoImplicit false
@[expose] public section

/-! A single Boolean field, copied in one step with a separate validity flag. -/

namespace JointThermoComplexity.Complexity.BooleanMachine
open _root_.Complexity
open _root_.Complexity.TM

def isBit : Γ → Bool
  | .zero | .one => true
  | _ => false

def accepted : List Bool → Bool
  | [] => false
  | _ :: _ => true

def copied : List Bool → List Bool
  | [] => []
  | bit :: _ => [bit]

def suffix : List Bool → List Bool
  | [] => []
  | _ :: rest => rest

theorem consumed_and_suffix (input : List Bool) : copied input ++ suffix input = input := by
  cases input <;> rfl

theorem codec_status_iff (input : List Bool) :
    accepted input = true ↔ ∃ bit tail, FiniteCodec.boolean.parse input = some (bit, tail) := by
  cases input <;> simp [accepted, FiniteCodec.boolean]

def action (n : ℕ) (si : Γ) (sw : Fin (n + 1) → Γ) (so : Γ) :
    Bool × (Fin (n + 1) → Γw) × Γw × Dir3 × (Fin (n + 1) → Dir3) × Dir3 :=
  (true, (NaturalMachine.finishAction n (isBit si) (isBit si) si sw so).2)

def machine (n : ℕ) : TM (n + 1) where
  Q := Bool
  qstart := false
  qhalt := true
  δ _ := action n
  δ_right_of_start _ si sw so := by
    cases si <;> simp [action, isBit, NaturalMachine.finishAction, idleDir]

variable {n : ℕ}

theorem bit_step (c : Cfg (n + 1) Bool) (bit : Bool)
    (hs : c.state = false) (hr : c.input.read = Γ.ofBool bit) :
    (machine n).step c = some {
      state := true, input := c.input.move .right, work := NaturalMachine.flaggedWork c.work true,
      output := c.output.writeAndMove (Γ.ofBool bit) .right } := by
  cases bit <;> simp [TM.step, machine, hs, hr, Γ.ofBool, action, isBit,
    NaturalMachine.finishAction, NaturalMachine.flaggedWork, transitionTape,
    readBackWrite, Γw.toΓ, funext_iff, apply_ite]
  all_goals intro i; split <;> simp_all [Γ.ofBool]

theorem eof_step (c : Cfg (n + 1) Bool) (hs : c.state = false) (hr : c.input.read = Γ.blank) :
    (machine n).step c = some {
      state := true, input := transitionInput c.input, work := NaturalMachine.flaggedWork c.work false,
      output := transitionTape c.output } := by
  simp [TM.step, machine, hs, hr, action, isBit, NaturalMachine.finishAction,
    NaturalMachine.flaggedWork, transitionInput, transitionTape, funext_iff, apply_ite]
  intro i
  split <;> simp_all [Γ.ofBool]

theorem run_from_cursor (before emitted remaining : List Bool) (c : Cfg (n + 1) Bool)
    (hs : c.state = false)
    (hcells : c.input.cells = (Tape.init ((before ++ remaining).map Γ.ofBool)).cells)
    (hhead : c.input.head = before.length + 1)
    (hw : ∀ i, (c.work i).read ≠ Γ.start)
    (hf : (c.work (NaturalMachine.flagIndex n)).head = 1)
    (hp : c.output.HasBinaryPrefix emitted) (hz : c.output.cells 0 = Γ.start) :
    ∃ d, (machine n).reachesIn 1 c d ∧ (machine n).halted d ∧
      d.input.cells = c.input.cells ∧ d.input.head = before.length + (copied remaining).length + 1 ∧
      (∀ i, i ≠ NaturalMachine.flagIndex n → d.work i = c.work i) ∧
      (d.work (NaturalMachine.flagIndex n)).head = 1 ∧
      (d.work (NaturalMachine.flagIndex n)).read = Γ.ofBool (accepted remaining) ∧
      d.output.cells 0 = Γ.start ∧ d.output.HasBinaryPrefix (emitted ++ copied remaining) := by
  cases remaining with
  | nil =>
    have hr : c.input.read = Γ.blank := by
      simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_ge before before.length le_rfl]
    have ho : c.output.read ≠ Γ.start := by
      have hb : c.output.read = Γ.blank := by simp [Tape.read, hp.1, hp.2.2 emitted.length le_rfl]
      simp [hb]
    let d : Cfg (n + 1) Bool := ⟨true, transitionInput c.input,
      NaturalMachine.flaggedWork c.work false, transitionTape c.output⟩
    have hi : d.input = c.input := transitionInput_eq_self (by simp [hr])
    have hout : d.output = c.output := transitionTape_eq_self ho
    refine ⟨d, .step (eof_step c hs hr) .zero, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [hi]
    · simpa only [hi, copied, List.length_nil, Nat.add_zero] using hhead
    · intro i h
      exact NaturalMachine.flaggedWork_other c.work false i h (hw i)
    · exact NaturalMachine.flaggedWork_head c.work false (hw _) hf
    · exact NaturalMachine.flaggedWork_read c.work false (hw _) hf
    · simpa only [hout] using hz
    · simpa only [hout, copied, List.append_nil] using hp
  | cons bit rest =>
    have hindex : before.length < (before ++ bit :: rest).length := by simp
    have hr : c.input.read = Γ.ofBool bit := by
      rw [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt _ before.length hindex]
      simp
    let d : Cfg (n + 1) Bool := ⟨true, c.input.move .right,
      NaturalMachine.flaggedWork c.work true, c.output.writeAndMove (Γ.ofBool bit) .right⟩
    refine ⟨d, .step (bit_step c bit hs hr) .zero, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [d, Tape.move, hhead, copied]
    · intro i h
      exact NaturalMachine.flaggedWork_other c.work true i h (hw i)
    · exact NaturalMachine.flaggedWork_head c.work true (hw _) hf
    · exact NaturalMachine.flaggedWork_read c.work true (hw _) hf
    · exact Tape.hasBinaryPrefix_write_bit_cell0 bit hp hz
    · exact Tape.hasBinaryPrefix_write_bit bit hp

end JointThermoComplexity.Complexity.BooleanMachine

#print axioms JointThermoComplexity.Complexity.BooleanMachine.codec_status_iff
#print axioms JointThermoComplexity.Complexity.BooleanMachine.run_from_cursor
