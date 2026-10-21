module
public import proofs.JointThermoComplexity.Complexity.BinaryEmitMachine

set_option autoImplicit false
@[expose] public section

/-! Append the literal bits of a binary work buffer without adding payload delimiters. -/

namespace JointThermoComplexity.Complexity.RawEmitMachine
open _root_.Complexity
open _root_.Complexity.TM
open BinaryEmitMachine

variable {w : ℕ}

def action (idx : Fin w) (q : State) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    State × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  match q, sw idx with
  | .read, .zero => emitAction idx .read false true si sw
  | .read, .one => emitAction idx .read true true si sw
  | _, _ => allReadBack .done si sw so

def machine (idx : Fin w) : TM w where
  Q := State
  qstart := .read
  qhalt := .done
  δ := action idx
  δ_right_of_start q si sw so := by
    cases q with
    | read =>
      cases h : sw idx <;> simp [action, h, emitAction, allReadBack, idleDir]
      all_goals
        intro j hj _
        exact hj
    | bit b => simp [action, allReadBack, idleDir]
    | done => simp [action, allReadBack, idleDir]

theorem bit_step (idx : Fin w) (c : Cfg w State) (bit : Bool) (hs : c.state = .read)
    (hr : (c.work idx).read = Γ.ofBool bit) :
    (machine idx).step c = some ⟨.read, transitionInput c.input, readWork idx c.work,
      c.output.writeAndMove (Γ.ofBool bit) .right⟩ := by
  cases bit <;> simp [TM.step, machine, action, emitAction, hs, hr, readWork, transitionInput,
    transitionTape, Γ.ofBool, Γw.ofBool, funext_iff]
  all_goals intro j; by_cases hj : j = idx <;> simp [hj]

theorem end_step (idx : Fin w) (c : Cfg w State) (hs : c.state = .read)
    (hr : (c.work idx).read = Γ.blank) :
    (machine idx).step c = some ⟨.done, transitionInput c.input,
      (fun j => transitionTape (c.work j)), transitionTape c.output⟩ := by
  simp [TM.step, machine, action, hs, hr, allReadBack, transitionInput, transitionTape]

end JointThermoComplexity.Complexity.RawEmitMachine

#print axioms JointThermoComplexity.Complexity.RawEmitMachine.bit_step
