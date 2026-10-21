module
public import proofs.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

set_option autoImplicit false
@[expose] public section

/-! One concrete initialization step followed by a checked machine body. -/

namespace JointThermoComplexity.Complexity.MachineEntry
open _root_.Complexity
open _root_.Complexity.TM

variable {n : ℕ}

def action (tm : TM n) (q : Option tm.Q) (si : Γ) (sw : Fin n → Γ) (so : Γ) :
    Option tm.Q × (Fin n → Γw) × Γw × Dir3 × (Fin n → Dir3) × Dir3 :=
  match q with
  | none => allReadBack (some tm.qstart) si sw so
  | some q =>
    let (q', ww, ow, di, dw, dout) := tm.δ q si sw so
    (some q', ww, ow, di, dw, dout)

def machine (tm : TM n) : TM n where
  Q := Option tm.Q
  finQ := {
    elems := {none} ∪ Finset.univ.image Option.some
    complete q := by cases q <;> simp }
  qstart := none
  qhalt := some tm.qhalt
  δ := action tm
  δ_right_of_start q si sw so := by
    cases q with
    | none => simp [action, allReadBack, idleDir]
    | some q => exact tm.δ_right_of_start q si sw so

def wrap (tm : TM n) (c : Cfg n tm.Q) : Cfg n (machine tm).Q :=
  ⟨some c.state, c.input, c.work, c.output⟩

def entered (tm : TM n) (c : Cfg n (machine tm).Q) : Cfg n tm.Q :=
  ⟨tm.qstart, transitionInput c.input, fun i => transitionTape (c.work i), transitionTape c.output⟩

theorem entry_step (tm : TM n) (c : Cfg n (machine tm).Q) (hs : c.state = none) :
    (machine tm).step c = some (wrap tm (entered tm c)) := by
  simp [TM.step, machine, action, hs, wrap, entered, allReadBack, transitionInput, transitionTape]

theorem body_step (tm : TM n) {c c' : Cfg n tm.Q} (h : tm.step c = some c') :
    (machine tm).step (wrap tm c) = some (wrap tm c') := by
  have hne := state_ne_qhalt_of_step h
  simp only [TM.step, hne, ↓reduceIte] at h
  have hc := Option.some.inj h
  subst c'
  simp [TM.step, machine, action, wrap, hne]

theorem body_reaches (tm : TM n) {t : ℕ} {c c' : Cfg n tm.Q}
    (h : tm.reachesIn t c c') :
    (machine tm).reachesIn t (wrap tm c) (wrap tm c') :=
  reachesIn_map (tm := tm) (tm' := machine tm) (wrap tm) (fun _ _ => body_step tm) h

theorem body_halted (tm : TM n) {c : Cfg n tm.Q} (h : tm.halted c) :
    (machine tm).halted (wrap tm c) := by
  change some c.state = some tm.qhalt
  exact congrArg Option.some h

theorem reaches (tm : TM n) (c : Cfg n (machine tm).Q) (hs : c.state = none)
    {t : ℕ} {d : Cfg n tm.Q} (h : tm.reachesIn t (entered tm c) d) :
    (machine tm).reachesIn (t + 1) c (wrap tm d) :=
  .step (entry_step tm c hs) (body_reaches tm h)

end JointThermoComplexity.Complexity.MachineEntry

#print axioms JointThermoComplexity.Complexity.MachineEntry.reaches
