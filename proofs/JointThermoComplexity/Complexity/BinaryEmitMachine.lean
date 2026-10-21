module
public import proofs.JointThermoComplexity.Complexity.BinaryTape
public import proofs.Complexitylib.Models.TuringMachine.Subroutines.Internal

set_option autoImplicit false
@[expose] public section

/-! Emit a delimited binary work payload while advancing its read cursor. -/

namespace JointThermoComplexity.Complexity.BinaryEmitMachine
open _root_.Complexity
open _root_.Complexity.TM

inductive State where
  | read | bit : Bool → State | done
  deriving DecidableEq

instance : Fintype State where
  elems := {.read, .bit false, .bit true, .done}
  complete q := by cases q with | bit b => cases b <;> simp | _ => simp

variable {w : ℕ}

def emitAction (idx : Fin w) (q : State) (b advance : Bool) (si : Γ) (sw : Fin w → Γ) :
    State × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (q, fun j => readBackWrite (sw j), Γw.ofBool b, idleDir si,
    fun j => if advance && decide (j = idx) then .right else idleDir (sw j), .right)

def action (idx : Fin w) (q : State) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    State × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  match q with
  | .read =>
    match sw idx with
    | .zero => emitAction idx (.bit false) true false si sw
    | .one => emitAction idx (.bit true) true false si sw
    | .blank => emitAction idx .done false false si sw
    | .start => allReadBack .done si sw so
  | .bit b => emitAction idx .read b true si sw
  | .done => allReadBack .done si sw so

def machine (idx : Fin w) : TM w where
  Q := State
  qstart := .read
  qhalt := .done
  δ := action idx
  δ_right_of_start q si sw so := by
    cases q with
    | read =>
      cases h : sw idx <;> simp [action, h, emitAction, idleDir, allReadBack]
    | bit b =>
      simp only [action, emitAction]
      refine ⟨idleDir_right_of_start, ?_, by simp⟩
      intro j hj
      by_cases heq : j = idx <;> simp [heq, hj, idleDir]
    | done => simp [action, allReadBack, idleDir]

def readWork (idx : Fin w) (work : Fin w → Tape) : Fin w → Tape := fun j =>
  if j = idx then (work j).writeAndMove (readBackWrite (work j).read) .right else transitionTape (work j)

theorem prefix_step (idx : Fin w) (c : Cfg w State) (b : Bool) (hs : c.state = .read)
    (hr : (c.work idx).read = Γ.ofBool b) :
    (machine idx).step c = some ⟨.bit b, transitionInput c.input,
      (fun j => transitionTape (c.work j)), c.output.writeAndMove Γ.one .right⟩ := by
  cases b <;> simp [TM.step, machine, action, emitAction, hs, hr, Γ.ofBool, Γw.ofBool,
    transitionInput, transitionTape]

theorem bit_step (idx : Fin w) (c : Cfg w State) (b : Bool) (hs : c.state = .bit b) :
    (machine idx).step c = some ⟨.read, transitionInput c.input, readWork idx c.work,
      c.output.writeAndMove (Γ.ofBool b) .right⟩ := by
  cases b <;> simp [TM.step, machine, action, emitAction, hs, readWork, transitionInput, transitionTape,
    Γw.ofBool, Γ.ofBool, funext_iff]
  all_goals intro j; by_cases hj : j = idx <;> simp [hj]

theorem end_step (idx : Fin w) (c : Cfg w State) (hs : c.state = .read) (hr : (c.work idx).read = Γ.blank) :
    (machine idx).step c = some ⟨.done, transitionInput c.input,
      (fun j => transitionTape (c.work j)), c.output.writeAndMove Γ.zero .right⟩ := by
  simp [TM.step, machine, action, emitAction, hs, hr, Γw.ofBool, transitionInput, transitionTape]

end JointThermoComplexity.Complexity.BinaryEmitMachine

#print axioms JointThermoComplexity.Complexity.BinaryEmitMachine.bit_step
