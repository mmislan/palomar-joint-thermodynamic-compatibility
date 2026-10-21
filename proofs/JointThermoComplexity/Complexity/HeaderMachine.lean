module
public import proofs.JointThermoComplexity.Complexity.IntegerMachine
public import proofs.JointThermoComplexity.Complexity.HeaderControl
public import proofs.Complexitylib.Models.TuringMachine.Registers

set_option autoImplicit false
@[expose] public section

/-!
# Dimension-header counter machine

True header bits extend a unary register; false ends the header. End-of-input
sets an invalid status. The existing checked rewind machine then parks the
counter at cell one. These counters are used for dimensions bounded by encoded
input length, never for binary exponent or factor values.
-/

namespace JointThermoComplexity.Complexity.HeaderMachine
open _root_.Complexity
open _root_.Complexity.TM

def counterIndex (n : ℕ) : Fin (n + 2) := (Fin.last n).castSucc
def flagIndex (n : ℕ) : Fin (n + 2) := NaturalMachine.flagIndex (n + 1)

theorem counter_ne_flag (n : ℕ) : counterIndex n ≠ flagIndex n := by
  intro h
  have hv := congrArg Fin.val h
  simp [counterIndex, flagIndex, NaturalMachine.flagIndex] at hv

inductive State where
  | start | count | rewind : RewindPhase → State | done
  deriving DecidableEq

instance : Fintype State where
  elems := {.start, .count, .done} ∪ Finset.univ.image State.rewind
  complete p := by cases p <;> simp

def wrapState (q : RewindPhase) : State := if q = .done then .done else .rewind q

def countAction (n : ℕ) (wHeads : Fin (n + 2) → Γ) :
    State × (Fin (n + 2) → Γw) × Γw × Dir3 × (Fin (n + 2) → Dir3) × Dir3 :=
  (.count, (fun i => if i = counterIndex n then .one else readBackWrite (wHeads i)),
    .one, .right, (fun i => if i = counterIndex n then .right else idleDir (wHeads i)), .right)

def action (n : ℕ) (q : State) (iHead : Γ) (wHeads : Fin (n + 2) → Γ) (oHead : Γ) :
    State × (Fin (n + 2) → Γw) × Γw × Dir3 × (Fin (n + 2) → Dir3) × Dir3 :=
  match q with
  | .start => allReadBack .count iHead wHeads oHead
  | .done => allReadBack .done iHead wHeads oHead
  | .count =>
    match iHead with
    | .one => countAction n wHeads
    | .zero => IntegerMachine.mapAction (fun _ => State.rewind .moveLeft)
        (NaturalMachine.finishAction (n + 1) true true iHead wHeads oHead)
    | _ => IntegerMachine.mapAction (fun _ => State.rewind .moveLeft)
        (NaturalMachine.finishAction (n + 1) false false iHead wHeads oHead)
  | .rewind q => IntegerMachine.mapAction wrapState ((rewindWorkTM (counterIndex n)).δ q iHead wHeads oHead)

def machine (n : ℕ) : TM (n + 2) where
  Q := State
  qstart := .start
  qhalt := .done
  δ := action n
  δ_right_of_start := by
    intro q iHead wHeads oHead
    cases q with
    | start => simp [action, allReadBack, idleDir]
    | done => simp [action, allReadBack, idleDir]
    | count =>
      cases iHead <;>
        simp [action, countAction, IntegerMachine.mapAction, NaturalMachine.finishAction, idleDir]
      intro i hi _
      exact hi
    | rewind q => exact (rewindWorkTM (counterIndex n)).δ_right_of_start q iHead wHeads oHead

variable {n : ℕ}

def growing (k : ℕ) : Tape := ⟨k + 1, regCells k⟩

theorem growing_read (k : ℕ) : (growing k).read = Γ.blank := by
  exact regCells_blank (Nat.le_refl _)

theorem growing_push (k : ℕ) : (growing k).writeAndMove Γ.one .right = growing (k + 1) := by
  apply Tape.ext
  · simp [growing, Tape.writeAndMove, Tape.write, Tape.move, Nat.add_assoc]
  · simpa only [growing, Tape.writeAndMove, Tape.move_cells, Tape.write,
      show k + 1 ≠ 0 from by omega, ↓reduceIte] using regCells_update_succ k

def pushedWork (w : Fin (n + 2) → Tape) (i : Fin (n + 2)) : Tape :=
  if i = counterIndex n then (w i).writeAndMove Γ.one .right else transitionTape (w i)

theorem count_step (c : Cfg (n + 2) (machine n).Q) (hs : c.state = .count)
    (hr : c.input.read = Γ.one) :
    (machine n).step c = some {
      state := .count, input := c.input.move .right, work := pushedWork c.work,
      output := c.output.writeAndMove Γ.one .right } := by
  simp [TM.step, machine, action, countAction, hs, hr, pushedWork, transitionTape, funext_iff, apply_ite]
  intro i
  split <;> simp_all

theorem terminator_step (c : Cfg (n + 2) (machine n).Q) (hs : c.state = .count)
    (hr : c.input.read = Γ.zero) :
    (machine n).step c = some {
      state := .rewind .moveLeft, input := c.input.move .right,
      work := NaturalMachine.flaggedWork c.work true,
      output := c.output.writeAndMove Γ.zero .right } := by
  simp [TM.step, machine, action, hs, hr, IntegerMachine.mapAction, NaturalMachine.finishAction,
    NaturalMachine.flaggedWork, transitionTape, funext_iff, apply_ite, readBackWrite, Γw.toΓ, Γ.ofBool]
  intro i
  split <;> simp_all

theorem eof_step (c : Cfg (n + 2) (machine n).Q) (hs : c.state = .count)
    (hr : c.input.read = Γ.blank) :
    (machine n).step c = some {
      state := .rewind .moveLeft, input := transitionInput c.input,
      work := NaturalMachine.flaggedWork c.work false, output := transitionTape c.output } := by
  simp [TM.step, machine, action, hs, hr, IntegerMachine.mapAction, NaturalMachine.finishAction,
    NaturalMachine.flaggedWork, transitionInput, transitionTape, funext_iff, apply_ite]
  intro i
  split <;> simp_all [Γ.ofBool]

def wrap (c : Cfg (n + 2) RewindPhase) : Cfg (n + 2) (machine n).Q :=
  ⟨wrapState c.state, c.input, c.work, c.output⟩

theorem rewind_step {c c' : Cfg (n + 2) RewindPhase}
    (hstep : (rewindWorkTM (counterIndex n)).step c = some c') :
    (machine n).step (wrap c) = some (wrap c') := by
  have hneq := state_ne_qhalt_of_step hstep
  have hne : c.state ≠ RewindPhase.done := hneq
  simp only [step, hneq, ↓reduceIte] at hstep
  have hcfg := Option.some.inj hstep
  subst c'
  simp [step, wrap, wrapState, hne, machine, action, IntegerMachine.mapAction]

theorem rewind_reaches {t : ℕ} {c c' : Cfg (n + 2) RewindPhase}
    (h : (rewindWorkTM (counterIndex n)).reachesIn t c c') :
    (machine n).reachesIn t (wrap c) (wrap c') :=
  reachesIn_map wrap (fun _ _ => rewind_step) h

theorem rewind_halted (c : Cfg (n + 2) RewindPhase)
    (h : (rewindWorkTM (counterIndex n)).halted c) : (machine n).halted (wrap c) := by
  change wrapState c.state = State.done
  change c.state = RewindPhase.done at h
  rw [h]
  rfl

end JointThermoComplexity.Complexity.HeaderMachine

#print axioms JointThermoComplexity.Complexity.HeaderMachine.machine
#print axioms JointThermoComplexity.Complexity.HeaderMachine.rewind_reaches
