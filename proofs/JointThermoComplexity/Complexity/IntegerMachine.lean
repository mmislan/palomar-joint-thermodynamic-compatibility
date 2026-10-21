module
public import proofs.JointThermoComplexity.Complexity.NaturalMachineParser

set_option autoImplicit false
@[expose] public section

/-!
# Sign dispatch into the canonical natural scanner

The sign selects the proved natural/positive payload machine. Negative zero is
therefore rejected by the same finite control, without expanding numeric values.
The state embedding maps the inner halt directly to the outer halt. The generic
checked `reachesIn_map` theorem supplies exact simulation, with no extra steps.
-/

namespace JointThermoComplexity.Complexity.IntegerMachine
open _root_.Complexity
open _root_.Complexity.TM

inductive State where
  | start | sign | body : Bool → NaturalMachine.State → State | done
  deriving DecidableEq

instance : Fintype State where
  elems := {.start, .sign, .done} ∪ Finset.univ.image (State.body false) ∪
    Finset.univ.image (State.body true)
  complete p := by cases p with | body sign q => cases sign <;> simp | _ => simp

def wrapState (sign : Bool) (q : NaturalMachine.State) : State :=
  if q = .done then .done else .body sign q

def mapAction {α β : Type} {k : ℕ} (f : α → β)
    (a : α × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3) :
    β × (Fin k → Γw) × Γw × Dir3 × (Fin k → Dir3) × Dir3 := (f a.1, a.2)

def signAction (n : ℕ) (sign : Bool) (iHead : Γ) (wHeads : Fin (n + 1) → Γ) :
    State × (Fin (n + 1) → Γw) × Γw × Dir3 × (Fin (n + 1) → Dir3) × Dir3 :=
  (.body sign .start, (fun i => readBackWrite (wHeads i)), readBackWrite iHead,
    .right, (fun i => idleDir (wHeads i)), .right)

def action (n : ℕ) (q : State) (iHead : Γ) (wHeads : Fin (n + 1) → Γ) (oHead : Γ) :
    State × (Fin (n + 1) → Γw) × Γw × Dir3 × (Fin (n + 1) → Dir3) × Dir3 :=
  match q with
  | .start => allReadBack .sign iHead wHeads oHead
  | .done => allReadBack .done iHead wHeads oHead
  | .sign =>
    match iHead with
    | .zero => signAction n false iHead wHeads
    | .one => signAction n true iHead wHeads
    | _ => mapAction (fun _ => State.done) (NaturalMachine.finishAction n false false iHead wHeads oHead)
  | .body sign q => mapAction (wrapState sign) ((NaturalMachine.machine sign n).δ q iHead wHeads oHead)

def machine (n : ℕ) : TM (n + 1) where
  Q := State
  qstart := .start
  qhalt := .done
  δ := action n
  δ_right_of_start := by
    intro q iHead wHeads oHead
    cases q with
    | start => simp [action, allReadBack, idleDir]
    | done => simp [action, allReadBack, idleDir]
    | sign => cases iHead <;>
        simp [action, signAction, mapAction, NaturalMachine.finishAction, idleDir]
    | body sign q =>
      exact (NaturalMachine.machine sign n).δ_right_of_start q iHead wHeads oHead

variable {n : ℕ}

def wrap (sign : Bool) (c : Cfg (n + 1) NaturalMachine.State) :
    Cfg (n + 1) (machine n).Q :=
  ⟨wrapState sign c.state, c.input, c.work, c.output⟩

theorem body_step (sign : Bool) {c c' : Cfg (n + 1) NaturalMachine.State}
    (hstep : (NaturalMachine.machine sign n).step c = some c') :
    (machine n).step (wrap sign c) = some (wrap sign c') := by
  have hneq := state_ne_qhalt_of_step hstep
  have hne : c.state ≠ NaturalMachine.State.done := hneq
  simp only [step, hneq, ↓reduceIte] at hstep
  have hcfg := Option.some.inj hstep
  subst c'
  simp [step, wrap, wrapState, hne, machine, action, mapAction]

theorem body_reaches (sign : Bool) {t : ℕ}
    {c c' : Cfg (n + 1) NaturalMachine.State}
    (h : (NaturalMachine.machine sign n).reachesIn t c c') :
    (machine n).reachesIn t (wrap sign c) (wrap sign c') :=
  reachesIn_map (wrap sign) (fun _ _ => body_step sign) h

theorem body_halted (sign : Bool) (c : Cfg (n + 1) NaturalMachine.State)
    (h : (NaturalMachine.machine sign n).halted c) : (machine n).halted (wrap sign c) := by
  change wrapState sign c.state = State.done
  change c.state = NaturalMachine.State.done at h
  rw [h]
  rfl

theorem sign_step (c : Cfg (n + 1) (machine n).Q) (sign : Bool)
    (hs : c.state = .sign) (hr : c.input.read = Γ.ofBool sign) :
    (machine n).step c = some {
      state := .body sign .start, input := c.input.move .right,
      work := fun i => transitionTape (c.work i),
      output := c.output.writeAndMove (Γ.ofBool sign) .right } := by
  cases sign <;>
    simp [TM.step, machine, action, signAction, hs, hr, Γ.ofBool, transitionTape, readBackWrite, Γw.toΓ]

theorem eof_step (c : Cfg (n + 1) (machine n).Q) (hs : c.state = .sign)
    (hr : c.input.read = Γ.blank) :
    (machine n).step c = some {
      state := .done, input := transitionInput c.input,
      work := NaturalMachine.flaggedWork c.work false, output := transitionTape c.output } := by
  simp [TM.step, machine, action, hs, hr, mapAction, NaturalMachine.finishAction,
    NaturalMachine.flaggedWork, transitionInput, transitionTape, funext_iff, apply_ite]
  intro i
  split <;> simp_all [Γ.ofBool]

end JointThermoComplexity.Complexity.IntegerMachine

#print axioms JointThermoComplexity.Complexity.IntegerMachine.body_reaches
#print axioms JointThermoComplexity.Complexity.IntegerMachine.machine
