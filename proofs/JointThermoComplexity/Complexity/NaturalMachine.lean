module
public import proofs.JointThermoComplexity.Complexity.PayloadFrame
public import proofs.JointThermoComplexity.Complexity.PayloadControl

set_option autoImplicit false
@[expose] public section

/-!
# A canonical-natural scanner with a work-tape status flag

The last work tape receives one Boolean status bit; every other off-marker work
tape is preserved. The finite control optionally rejects zero for positive-factor
fields. Output copies the structural payload prefix, with validity communicated
separately to the surrounding parser. No represented value is expanded.
-/

namespace JointThermoComplexity.Complexity.NaturalMachine
open _root_.Complexity
open _root_.Complexity.TM
open PayloadControl

inductive State where
  | start | read : ReadState → State | done
  deriving DecidableEq

instance : Fintype State where
  elems := {.start, .read .empty, .read .zero, .read .one, .read .payload, .done}
  complete s := by cases s with | read p => cases p <;> simp | _ => simp

def flagIndex (n : ℕ) : Fin (n + 1) := Fin.last n

def copyAction (n : ℕ) (q : ReadState) (iHead : Γ) (wHeads : Fin (n + 1) → Γ) :
    State × (Fin (n + 1) → Γw) × Γw × Dir3 × (Fin (n + 1) → Dir3) × Dir3 :=
  (.read q, (fun i => readBackWrite (wHeads i)), readBackWrite iHead, .right,
    (fun i => idleDir (wHeads i)), .right)

def finishAction (n : ℕ) (copyBit valid : Bool) (iHead : Γ)
    (wHeads : Fin (n + 1) → Γ) (oHead : Γ) :
    State × (Fin (n + 1) → Γw) × Γw × Dir3 × (Fin (n + 1) → Dir3) × Dir3 :=
  (.done, (fun i => if i = flagIndex n then (if valid then .one else .zero)
    else readBackWrite (wHeads i)),
    (if copyBit then readBackWrite iHead else readBackWrite oHead),
    (if copyBit then .right else idleDir iHead),
    (fun i => idleDir (wHeads i)), (if copyBit then .right else idleDir oHead))

def action (requirePositive : Bool) (n : ℕ) (state : State) (iHead : Γ)
    (wHeads : Fin (n + 1) → Γ) (oHead : Γ) :
    State × (Fin (n + 1) → Γw) × Γw × Dir3 × (Fin (n + 1) → Dir3) × Dir3 :=
  match state with
  | .start => allReadBack (.read .empty) iHead wHeads oHead
  | .done => allReadBack .done iHead wHeads oHead
  | .read p =>
    match iHead with
    | .zero =>
      match next p false with
      | none => finishAction n true (accept requirePositive p) iHead wHeads oHead
      | some q => copyAction n q iHead wHeads
    | .one =>
      match next p true with
      | none => finishAction n true (accept requirePositive p) iHead wHeads oHead
      | some q => copyAction n q iHead wHeads
    | _ => finishAction n false false iHead wHeads oHead

def machine (requirePositive : Bool) (n : ℕ) : TM (n + 1) where
  Q := State
  qstart := .start
  qhalt := .done
  δ := action requirePositive n
  δ_right_of_start := by
    intro state iHead wHeads oHead
    cases state with
    | start => simp [action, allReadBack, idleDir]
    | done => simp [action, allReadBack, idleDir]
    | read p =>
      cases p <;> cases iHead <;>
        simp [action, PayloadControl.next, copyAction, finishAction, idleDir]

variable {n : ℕ}

def flaggedWork (w : Fin (n + 1) → Tape) (valid : Bool) (i : Fin (n + 1)) : Tape :=
  if i = flagIndex n then (w i).writeAndMove (Γ.ofBool valid) (idleDir (w i).read)
    else transitionTape (w i)

theorem flaggedWork_other (w : Fin (n + 1) → Tape) (valid : Bool) (i : Fin (n + 1))
    (hi : i ≠ flagIndex n) (hread : (w i).read ≠ Γ.start) : flaggedWork w valid i = w i := by
  rw [flaggedWork, ite_eq_right hi]
  exact transitionTape_eq_self hread

theorem flaggedWork_head (w : Fin (n + 1) → Tape) (valid : Bool)
    (hread : (w (flagIndex n)).read ≠ Γ.start) (hhead : (w (flagIndex n)).head = 1) :
    (flaggedWork w valid (flagIndex n)).head = 1 := by
  simp [flaggedWork, idleDir, hread, Tape.writeAndMove, Tape.move, Tape.write, hhead]

theorem flaggedWork_read (w : Fin (n + 1) → Tape) (valid : Bool)
    (hread : (w (flagIndex n)).read ≠ Γ.start) (hhead : (w (flagIndex n)).head = 1) :
    (flaggedWork w valid (flagIndex n)).read = Γ.ofBool valid := by
  have hcell : (w (flagIndex n)).cells 1 ≠ Γ.start := by simpa only [Tape.read, hhead] using hread
  simp [flaggedWork, idleDir, Tape.read, Tape.writeAndMove, Tape.move, Tape.write, hhead, hcell]

theorem continue_step (requirePositive : Bool) (c : Cfg (n + 1) (machine requirePositive n).Q)
    (p q : ReadState) (bit : Bool) (hs : c.state = .read p)
    (hr : c.input.read = Γ.ofBool bit) (hnext : next p bit = some q) :
    (machine requirePositive n).step c = some {
      state := .read q, input := c.input.move .right,
      work := fun i => transitionTape (c.work i),
      output := c.output.writeAndMove (Γ.ofBool bit) .right } := by
  cases bit <;>
    simp [TM.step, machine, hs, hr, Γ.ofBool, action, hnext, copyAction, transitionTape,
      readBackWrite, Γw.toΓ]

theorem finish_step (requirePositive : Bool) (c : Cfg (n + 1) (machine requirePositive n).Q)
    (p : ReadState) (bit : Bool) (hs : c.state = .read p)
    (hr : c.input.read = Γ.ofBool bit) (hnext : next p bit = none) :
    (machine requirePositive n).step c = some {
      state := .done, input := c.input.move .right,
      work := flaggedWork c.work (accept requirePositive p),
      output := c.output.writeAndMove (Γ.ofBool bit) .right } := by
  cases bit <;>
    simp [TM.step, machine, hs, hr, Γ.ofBool, action, hnext, finishAction, flaggedWork,
      transitionTape, readBackWrite, Γw.toΓ, funext_iff, apply_ite]
  all_goals intro i; split <;> cases hacc : accept requirePositive p <;> simp_all [Γ.ofBool]

theorem eof_step (requirePositive : Bool) (c : Cfg (n + 1) (machine requirePositive n).Q)
    (p : ReadState) (hs : c.state = .read p) (hr : c.input.read = Γ.blank) :
    (machine requirePositive n).step c = some {
      state := .done, input := transitionInput c.input,
      work := flaggedWork c.work false, output := transitionTape c.output } := by
  simp [TM.step, machine, hs, hr, action, finishAction, flaggedWork, transitionInput,
    transitionTape, funext_iff, apply_ite]
  intro i
  split <;> simp_all [Γ.ofBool]

end JointThermoComplexity.Complexity.NaturalMachine

#print axioms JointThermoComplexity.Complexity.NaturalMachine.machine
#print axioms JointThermoComplexity.Complexity.NaturalMachine.finish_step
