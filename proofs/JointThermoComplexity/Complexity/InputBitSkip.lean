module
public import proofs.JointThermoComplexity.Complexity.NaturalSkipRaw
public import proofs.JointThermoComplexity.Complexity.BooleanMachine

set_option autoImplicit false
@[expose] public section

/-! Skip one available bit without changing any work or output tape; end of input remains in place. -/

namespace JointThermoComplexity.Complexity.InputBitSkip
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def action (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (true, (fun j => readBackWrite (sw j)), readBackWrite so,
    (if BooleanMachine.isBit si then .right else idleDir si), (fun j => idleDir (sw j)), idleDir so)

def machine : TM w where
  Q := Bool
  qstart := false
  qhalt := true
  δ _ := action
  δ_right_of_start _ _ _ _ :=
    ⟨by intro h; rw [h]; rfl, fun _ hj => idleDir_right_of_start hj, idleDir_right_of_start⟩

theorem step (c : Cfg w (machine (w := w)).Q) (hs : c.state = false)
    (hi : c.input.read ≠ Γ.start) (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    machine.step c = some ⟨true, c.input.move (if BooleanMachine.isBit c.input.read then .right else .stay),
      c.work, c.output⟩ := by
  have hd : machine.δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      action c.input.read (fun j => (c.work j).read) c.output.read := rfl
  rw [TM.step, ite_eq_right (by simp [machine, hs]), hd]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · change c.input.move (if BooleanMachine.isBit c.input.read then .right else idleDir c.input.read) = _
    rw [idleDir, ite_eq_right hi]
  · exact funext (fun j => transitionTape_eq_self (hw j))
  · exact transitionTape_eq_self ho

theorem hoareTime (before input emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ R work out)
      (fun inp work out => Cursor (before ++ input.take 1) (input.drop 1) emitted inp work out ∧ R work out) 1 := by
  rintro inp work out ⟨hc, hr⟩
  let c : Cfg w (machine (w := w)).Q := ⟨false, inp, work, out⟩
  have hs := step c rfl hc.input_read (fun j => (hc.works j).1) hc.output_read
  cases input with
  | nil =>
    have hi : inp.read = Γ.blank := by
      have hcells : inp.cells = (Tape.init (before.map Γ.ofBool)).cells := by simpa only [List.append_nil] using hc.cells
      simp [Tape.read, hc.head, hcells, Tape.init_ofBool_cells_ge before before.length le_rfl]
    have hstep : machine.step c = some ⟨true, inp, work, out⟩ := by simpa [c, hi, BooleanMachine.isBit, Tape.move] using hs
    refine ⟨⟨true, inp, work, out⟩, 1, le_rfl, .step hstep .zero, rfl, ?_, hr⟩
    simpa only [List.take_nil, List.drop_nil, List.append_nil] using hc
  | cons bit tail =>
    have hi := InputCursor.read_bit bit hc
    have hstep : machine.step c = some ⟨true, inp.move .right, work, out⟩ := by
      cases bit <;> simpa [c, hi, BooleanMachine.isBit, Γ.ofBool] using hs
    refine ⟨⟨true, inp.move .right, work, out⟩, 1, le_rfl, .step hstep .zero, rfl, ?_, hr⟩
    simpa only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero] using InputCursor.consume bit hc

end JointThermoComplexity.Complexity.InputBitSkip

#print axioms JointThermoComplexity.Complexity.InputBitSkip.hoareTime
