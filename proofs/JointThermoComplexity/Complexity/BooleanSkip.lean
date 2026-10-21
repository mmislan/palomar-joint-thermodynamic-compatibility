module
public import proofs.JointThermoComplexity.Complexity.InputCursor
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! A one-bit input advance preserves every work tape and the output tape exactly. -/

namespace JointThermoComplexity.Complexity.BooleanSkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop

variable {w : ℕ}

def machine : TM w where
  Q := Bool
  qstart := false
  qhalt := true
  δ _ _ sw so := (true, (fun j => readBackWrite (sw j)), readBackWrite so,
    .right, (fun j => idleDir (sw j)), idleDir so)
  δ_right_of_start _ _ _ _ :=
    ⟨fun _ => rfl, fun _ hj => idleDir_right_of_start hj, idleDir_right_of_start⟩

theorem bit_step (c : Cfg w (machine (w := w)).Q) (hs : c.state = false)
    (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    machine.step c = some ⟨true, c.input.move .right, c.work, c.output⟩ := by
  rw [TM.step, ite_eq_right (by simp [machine, hs])]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · exact funext (fun j => transitionTape_eq_self (hw j))
  · exact transitionTape_eq_self ho

theorem framed (r : Fin w) (v head : ℕ) (hh : 1 ≤ head) (bit : Bool)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine (w := w)).HoareTime
      (Frame r v head (fun inp work out => Cursor before (bit :: tail) emitted inp work out ∧ R work out))
      (Frame r v head (fun inp work out => Cursor (before ++ [bit]) tail emitted inp work out ∧ R work out)) 1 := by
  intro inp work out hf
  let c : Cfg w (machine (w := w)).Q := ⟨false, inp, work, out⟩
  let d : Cfg w (machine (w := w)).Q := ⟨true, inp.move .right, work, out⟩
  have hreads : ∀ j, (work j).read ≠ Γ.start := by
    intro j
    by_cases hj : j = r
    · subst j
      rw [hf.fuel]
      exact regCells_ne_start hh
    · exact hf.readOthers j hj
  have hstep : machine.step c = some d := bit_step c rfl hreads hf.readOutput
  have hc := InputCursor.consume bit hf.invariant.1
  exact ⟨d, 1, le_rfl, .step hstep .zero, rfl, hf.fuel, hc.input_read,
    hf.readOthers, hf.readOutput, hc, hf.invariant.2⟩

end JointThermoComplexity.Complexity.BooleanSkip

#print axioms JointThermoComplexity.Complexity.BooleanSkip.framed
