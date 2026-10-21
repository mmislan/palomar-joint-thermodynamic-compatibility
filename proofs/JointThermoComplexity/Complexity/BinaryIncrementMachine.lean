module
public import proofs.JointThermoComplexity.Complexity.IntegerMachine
public import proofs.Complexitylib.Models.TuringMachine.Subroutines.Internal

set_option autoImplicit false
@[expose] public section

/-! In-place little-endian increment, followed by the checked work-tape rewind. -/

namespace JointThermoComplexity.Complexity.BinaryIncrementMachine
open _root_.Complexity
open _root_.Complexity.TM

inductive State where
  | carry | rewind : RewindPhase → State | done
  deriving DecidableEq

instance : Fintype State where
  elems := {.carry, .done} ∪ Finset.univ.image State.rewind
  complete q := by cases q <;> simp

def wrapState : RewindPhase → State
  | .done => .done
  | q => .rewind q

variable {w : ℕ}

def carryAction (idx : Fin w) (q : State) (bit : Bool) (dir : Dir3)
    (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    State × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (q, fun j => if j = idx then Γw.ofBool bit else readBackWrite (sw j), readBackWrite so,
    idleDir si, fun j => if j = idx then dir else idleDir (sw j), idleDir so)

def action (idx : Fin w) (q : State) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    State × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  match q with
  | .carry =>
    match sw idx with
    | .one => carryAction idx .carry false .right si sw so
    | .zero | .blank => carryAction idx (.rewind .moveLeft) true .stay si sw so
    | .start => allReadBack .done si sw so
  | .rewind q => IntegerMachine.mapAction wrapState ((rewindWorkTM idx).δ q si sw so)
  | .done => allReadBack .done si sw so

def machine (idx : Fin w) : TM w where
  Q := State
  qstart := .carry
  qhalt := .done
  δ := action idx
  δ_right_of_start q si sw so := by
    cases q with
    | carry =>
      cases h : sw idx <;> simp only [action, h]
      all_goals try exact rightOfStart_allReadBack si sw so
      all_goals
        refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
        intro j hj
        by_cases heq : j = idx
        · subst j
          simp_all
        · simpa [carryAction, heq] using idleDir_right_of_start hj
    | rewind q => exact (rewindWorkTM idx).δ_right_of_start q si sw so
    | done => simp [action, allReadBack, idleDir]

def changedWork (idx : Fin w) (bit : Bool) (dir : Dir3) (work : Fin w → Tape) : Fin w → Tape := fun j =>
  if j = idx then (work j).writeAndMove (Γ.ofBool bit) dir else transitionTape (work j)

theorem carry_step (idx : Fin w) (c : Cfg w State) (hs : c.state = .carry)
    (hr : (c.work idx).read = Γ.one) :
    (machine idx).step c = some ⟨.carry, transitionInput c.input, changedWork idx false .right c.work, transitionTape c.output⟩ := by
  simp [TM.step, machine, action, carryAction, hs, hr, changedWork, transitionInput, transitionTape,
    funext_iff, apply_ite]
  intro j
  split <;> simp_all [Γ.ofBool, Γw.ofBool]

theorem finish_step (idx : Fin w) (c : Cfg w State) (hs : c.state = .carry)
    (hr : (c.work idx).read = Γ.zero ∨ (c.work idx).read = Γ.blank) :
    (machine idx).step c = some ⟨.rewind .moveLeft, transitionInput c.input,
      changedWork idx true .stay c.work, transitionTape c.output⟩ := by
  rcases hr with hr | hr <;>
    simp [TM.step, machine, action, carryAction, hs, hr, changedWork, transitionInput, transitionTape,
      funext_iff, apply_ite]
  all_goals intro j; split <;> simp_all [Γ.ofBool, Γw.ofBool]

def wrap (idx : Fin w) (c : Cfg w RewindPhase) : Cfg w (machine idx).Q :=
  ⟨wrapState c.state, c.input, c.work, c.output⟩

theorem rewind_step (idx : Fin w) {c c' : Cfg w RewindPhase} (h : (rewindWorkTM idx).step c = some c') :
    (machine idx).step (wrap idx c) = some (wrap idx c') := by
  have hne := state_ne_qhalt_of_step h
  have hne' : c.state ≠ RewindPhase.done := hne
  simp only [TM.step, hne, ↓reduceIte] at h
  have hc := Option.some.inj h
  subst c'
  cases hs : c.state <;> simp_all [TM.step, machine, wrap, wrapState, action, IntegerMachine.mapAction]

theorem rewind_reaches (idx : Fin w) {t : ℕ} {c c' : Cfg w RewindPhase}
    (h : (rewindWorkTM idx).reachesIn t c c') :
    (machine idx).reachesIn t (wrap idx c) (wrap idx c') :=
  reachesIn_map (wrap idx) (fun _ _ => rewind_step idx) h

theorem rewind_halted (idx : Fin w) {c : Cfg w RewindPhase} (h : (rewindWorkTM idx).halted c) :
    (machine idx).halted (wrap idx c) := by
  change wrapState c.state = State.done
  rw [h]
  rfl

end JointThermoComplexity.Complexity.BinaryIncrementMachine

#print axioms JointThermoComplexity.Complexity.BinaryIncrementMachine.rewind_reaches
