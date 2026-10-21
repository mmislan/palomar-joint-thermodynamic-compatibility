module
public import proofs.JointThermoComplexity.Complexity.InputCursor

set_option autoImplicit false
@[expose] public section

/-! Decode the self-delimiting natural payload into raw binary digits, without expanding its value. -/

namespace JointThermoComplexity.Complexity.NaturalRawMachine
open _root_.Complexity
open _root_.Complexity.TM

variable {w : ℕ}

def copyAction (q : Option Bool) (emit : Bool) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Option Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (q, fun j => readBackWrite (sw j), if emit then readBackWrite si else readBackWrite so,
    .right, fun j => idleDir (sw j), if emit then .right else idleDir so)

def action (q : Option Bool) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Option Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  match q with
  | none => allReadBack none si sw so
  | some false => match si with
      | .zero => copyAction none false si sw so
      | .one => copyAction (some true) false si sw so
      | _ => allReadBack none si sw so
  | some true => match si with
      | .zero | .one => copyAction (some false) true si sw so
      | _ => allReadBack none si sw so

def machine : TM w where
  Q := Option Bool
  qstart := some false
  qhalt := none
  δ := action
  δ_right_of_start q si sw so := by
    cases q with
    | none => exact rightOfStart_allReadBack si sw so
    | some b => cases b <;> cases si <;> simp [action, copyAction, allReadBack, idleDir]

theorem flag_step (bit : Bool) (c : Cfg w (Option Bool)) (hs : c.state = some false)
    (hr : c.input.read = Γ.ofBool bit) (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine (w := w)).step c = some ⟨if bit then some true else none, c.input.move .right, c.work, c.output⟩ := by
  cases bit <;>
    simp [TM.step, machine, action, copyAction, hs, hr, Γ.ofBool]
  all_goals
    constructor
    · exact funext (fun j => transitionTape_eq_self (hw j))
    · exact transitionTape_eq_self ho

theorem payload_step (bit : Bool) (c : Cfg w (Option Bool)) (hs : c.state = some true)
    (hr : c.input.read = Γ.ofBool bit) (hw : ∀ j, (c.work j).read ≠ Γ.start) :
    (machine (w := w)).step c = some ⟨some false, c.input.move .right, c.work,
      c.output.writeAndMove (Γ.ofBool bit) .right⟩ := by
  cases bit <;>
    simp [TM.step, machine, action, copyAction, hs, hr, Γ.ofBool, readBackWrite, Γw.toΓ]
  all_goals exact funext (fun j => transitionTape_eq_self (hw j))

end JointThermoComplexity.Complexity.NaturalRawMachine

#print axioms JointThermoComplexity.Complexity.NaturalRawMachine.flag_step
#print axioms JointThermoComplexity.Complexity.NaturalRawMachine.payload_step
