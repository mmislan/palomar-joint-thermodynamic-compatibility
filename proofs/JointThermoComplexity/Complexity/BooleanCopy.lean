module
public import proofs.JointThermoComplexity.Complexity.InputCursor

set_option autoImplicit false
@[expose] public section

/-! Copy one actual input bit without changing any work tape. -/

namespace JointThermoComplexity.Complexity.BooleanCopy
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine : TM w where
  Q := Bool
  qstart := false
  qhalt := true
  δ _ si sw _ := (true, (fun j => readBackWrite (sw j)), readBackWrite si,
    .right, (fun j => idleDir (sw j)), .right)
  δ_right_of_start _ _ _ _ :=
    ⟨fun _ => rfl, fun _ hj => idleDir_right_of_start hj, fun _ => rfl⟩

theorem bit_step (bit : Bool) (c : Cfg w (machine (w := w)).Q) (hs : c.state = false)
    (hr : c.input.read = Γ.ofBool bit) (hw : ∀ j, (c.work j).read ≠ Γ.start) :
    machine.step c = some ⟨true, c.input.move .right, c.work,
      c.output.writeAndMove (Γ.ofBool bit) .right⟩ := by
  rw [TM.step, ite_eq_right (by simp [machine, hs])]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · exact funext (fun j => transitionTape_eq_self (hw j))
  · cases bit <;> simp [machine, hr, Γ.ofBool, readBackWrite]

theorem hoareTime (bit : Bool) (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before (bit :: tail) emitted inp work out ∧ R work)
      (fun inp work out => Cursor (before ++ [bit]) tail (emitted ++ [bit]) inp work out ∧ R work) 1 := by
  rintro inp work out ⟨hc, hr⟩
  let d : Cfg w (machine (w := w)).Q :=
    ⟨true, inp.move .right, work, out.writeAndMove (Γ.ofBool bit) .right⟩
  have hs : machine.step ⟨false, inp, work, out⟩ = some d :=
    bit_step bit _ rfl (InputCursor.read_bit bit hc) (fun j => (hc.works j).1)
  have hcur := InputCursor.consume bit hc
  exact ⟨d, 1, le_rfl, .step hs .zero, rfl,
    ⟨hcur.cells, hcur.head, hcur.works, Tape.hasBinaryPrefix_write_bit bit hc.tapePrefix,
      Tape.hasBinaryPrefix_write_bit_cell0 bit hc.tapePrefix hc.zero⟩, hr⟩

end JointThermoComplexity.Complexity.BooleanCopy

#print axioms JointThermoComplexity.Complexity.BooleanCopy.hoareTime
