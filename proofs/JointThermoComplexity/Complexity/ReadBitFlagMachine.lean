module
public import proofs.JointThermoComplexity.Complexity.InputCursor

set_option autoImplicit false
@[expose] public section

/-! Consume one actual input bit into a work flag without appending any formula output. -/

namespace JointThermoComplexity.Complexity.ReadBitFlagMachine
open _root_.Complexity
open _root_.Complexity.TM

variable {w : ℕ}

def asWrite : Γ → Γw
  | .one => .one
  | _ => .zero

theorem asWrite_ofBool (bit : Bool) : (asWrite (Γ.ofBool bit)).toΓ = Γ.ofBool bit := by
  cases bit <;> rfl

def action (flag : Fin w) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (true, (fun j => if j = flag then asWrite si else readBackWrite (sw j)), readBackWrite so,
    .right, (fun j => idleDir (sw j)), idleDir so)

def machine (flag : Fin w) : TM w where
  Q := Bool
  qstart := false
  qhalt := true
  δ _ := action flag
  δ_right_of_start _ _ _ _ :=
    ⟨fun _ => rfl, fun _ hj => idleDir_right_of_start hj, idleDir_right_of_start⟩

theorem bit_step (flag : Fin w) (bit : Bool) (c : Cfg w (machine flag).Q)
    (hs : c.state = false) (hr : c.input.read = Γ.ofBool bit)
    (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine flag).step c = some ⟨true, c.input.move .right,
      Function.update c.work flag ((c.work flag).write (Γ.ofBool bit)), c.output⟩ := by
  have hδ : (machine flag).δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      action flag c.input.read (fun j => (c.work j).read) c.output.read := rfl
  rw [TM.step, ite_eq_right (by simp [machine, hs]), hδ]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    change (c.work j).writeAndMove
      ((if j = flag then asWrite c.input.read else readBackWrite (c.work j).read).toΓ)
      (idleDir (c.work j).read) = Function.update c.work flag ((c.work flag).write (Γ.ofBool bit)) j
    by_cases hj : j = flag
    · subst j
      rw [ite_eq_left rfl, Function.update_self, hr, asWrite_ofBool]
      rw [idleDir, ite_eq_right (hw flag)]
      rfl
    · rw [ite_eq_right hj, Function.update_of_ne hj]
      exact transitionTape_eq_self (hw j)
  · exact transitionTape_eq_self ho

end JointThermoComplexity.Complexity.ReadBitFlagMachine

#print axioms JointThermoComplexity.Complexity.ReadBitFlagMachine.bit_step
