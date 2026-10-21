module
public import proofs.JointThermoComplexity.Complexity.ScannerSpec

set_option autoImplicit false
@[expose] public section

/-! Actual input-tag dispatch for optional records, including missing-tag failure. -/

namespace JointThermoComplexity.Complexity.OptionalMachine
open _root_.Complexity
open _root_.Complexity.TM

inductive State (Q : Type) where
  | tag | body : Q → State Q | done
  deriving DecidableEq

instance {Q : Type} [Fintype Q] [DecidableEq Q] : Fintype (State Q) where
  elems := {.tag, .done} ∪ Finset.univ.image State.body
  complete q := by cases q <;> simp

variable {w : ℕ}

def wrapState (tm : TM w) (q : tm.Q) : State tm.Q :=
  if q = tm.qhalt then .done else .body q

def tagAction (tm : TM w) (master flag : Fin w) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    State tm.Q × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  match si with
  | .one => (.body tm.qstart, fun j => readBackWrite (sw j), .one, .right,
      fun j => idleDir (sw j), .right)
  | .zero => (.done, fun j => if j = flag then .one else readBackWrite (sw j), .zero, .right,
      fun j => idleDir (sw j), .right)
  | _ => (.done, fun j => if j = flag ∨ j = master then .zero else readBackWrite (sw j),
      readBackWrite so, idleDir si, fun j => idleDir (sw j), idleDir so)

def action (tm : TM w) (master flag : Fin w) (q : State tm.Q) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    State tm.Q × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  match q with
  | .tag => tagAction tm master flag si sw so
  | .body q => IntegerMachine.mapAction (wrapState tm) (tm.δ q si sw so)
  | .done => allReadBack .done si sw so

def machine (tm : TM w) (master flag : Fin w) : TM w where
  Q := State tm.Q
  qstart := .tag
  qhalt := .done
  δ := action tm master flag
  δ_right_of_start q si sw so := by
    cases q with
    | tag => cases si <;> simp [action, tagAction, idleDir]
    | body q => exact tm.δ_right_of_start q si sw so
    | done => simp [action, allReadBack, idleDir]

def wrap (tm : TM w) (master flag : Fin w) (c : Cfg w tm.Q) : Cfg w (machine tm master flag).Q :=
  ⟨wrapState tm c.state, c.input, c.work, c.output⟩

theorem body_step (tm : TM w) (master flag : Fin w) {c c' : Cfg w tm.Q}
    (h : tm.step c = some c') :
    (machine tm master flag).step (wrap tm master flag c) = some (wrap tm master flag c') := by
  have hne := state_ne_qhalt_of_step h
  simp only [TM.step, hne, ↓reduceIte] at h
  have hc := Option.some.inj h
  subst c'
  simp [TM.step, wrap, wrapState, hne, machine, action, IntegerMachine.mapAction]

theorem body_reaches (tm : TM w) (master flag : Fin w) {t : ℕ} {c c' : Cfg w tm.Q}
    (h : tm.reachesIn t c c') :
    (machine tm master flag).reachesIn t (wrap tm master flag c) (wrap tm master flag c') :=
  reachesIn_map (tm := tm) (tm' := machine tm master flag) (wrap tm master flag)
    (fun _ _ => body_step tm master flag) h

theorem body_halted (tm : TM w) (master flag : Fin w) {c : Cfg w tm.Q} (h : tm.halted c) :
    (machine tm master flag).halted (wrap tm master flag c) := by
  change wrapState tm c.state = State.done
  rw [h]
  simp [wrapState]

def taggedWork (work : Fin w → Tape) (master flag : Fin w) (good : Bool) : Fin w → Tape := fun j =>
  if j = flag then (work j).writeAndMove (Γ.ofBool good) (idleDir (work j).read)
  else if good = false ∧ j = master then (work j).writeAndMove Γ.zero (idleDir (work j).read)
  else transitionTape (work j)

theorem some_step (tm : TM w) (master flag : Fin w) (c : Cfg w (State tm.Q))
    (hs : c.state = .tag) (hr : c.input.read = Γ.one) :
    (machine tm master flag).step c = some {
      state := .body tm.qstart, input := c.input.move .right,
      work := fun j => transitionTape (c.work j), output := c.output.writeAndMove Γ.one .right } := by
  simp [TM.step, machine, action, tagAction, hs, hr, transitionTape]

theorem none_step (tm : TM w) (master flag : Fin w) (c : Cfg w (State tm.Q))
    (hs : c.state = .tag) (hr : c.input.read = Γ.zero) :
    (machine tm master flag).step c = some {
      state := .done, input := c.input.move .right, work := taggedWork c.work master flag true,
      output := c.output.writeAndMove Γ.zero .right } := by
  simp [TM.step, machine, action, tagAction, hs, hr, taggedWork, transitionTape,
    funext_iff, apply_ite]
  intro j
  split <;> simp_all [Γ.ofBool]

theorem eof_step (tm : TM w) (master flag : Fin w) (c : Cfg w (State tm.Q))
    (hs : c.state = .tag) (hr : c.input.read = Γ.blank) :
    (machine tm master flag).step c = some {
      state := .done, input := transitionInput c.input, work := taggedWork c.work master flag false,
      output := transitionTape c.output } := by
  simp [TM.step, machine, action, tagAction, hs, hr, transitionTape,
    transitionInput, funext_iff]
  intro j
  by_cases hj : j = flag <;> by_cases hm : j = master <;>
    simp [taggedWork, hj, hm, Γ.ofBool, transitionTape]

end JointThermoComplexity.Complexity.OptionalMachine

#print axioms JointThermoComplexity.Complexity.OptionalMachine.body_reaches
#print axioms JointThermoComplexity.Complexity.OptionalMachine.eof_step
