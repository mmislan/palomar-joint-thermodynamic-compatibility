module
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceMachine

set_option autoImplicit false
@[expose] public section

/-! Exact TM transitions consume actual operand bits, pad blank suffixes with zero and retain the final borrow. -/

namespace JointThermoComplexity.Complexity.BinaryDifferenceStep
open _root_.Complexity
open _root_.Complexity.TM
open BinaryBorrow BinaryDifferenceMachine

variable {w : ℕ}

theorem data_step (left right flag : Fin w) (emit carry : Bool) (a b : Option Bool)
    (c : Cfg w (machine left right flag emit).Q) (hs : c.state = some carry)
    (hl : (c.work left).read = symbol a) (hr : (c.work right).read = symbol b)
    (hne : a ≠ none ∨ b ≠ none) :
    (machine left right flag emit).step c = some
      ⟨some (borrow (a.getD false) (b.getD false) carry), transitionInput c.input, dataWork left right c.work,
        if emit then c.output.writeAndMove (Γ.ofBool (digit (a.getD false) (b.getD false) carry)) .right else transitionTape c.output⟩ := by
  have hend : ¬((c.work left).read = Γ.blank ∧ (c.work right).read = Γ.blank) := by
    rintro ⟨hleft, hright⟩
    have ha := (symbol_blank a).mp (hl.symm.trans hleft)
    have hb := (symbol_blank b).mp (hr.symm.trans hright)
    rcases hne with h | h
    · exact h ha
    · exact h hb
  have hδ : (machine left right flag emit).δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      (some (borrow (a.getD false) (b.getD false) carry), (fun j => readBackWrite (c.work j).read),
        (if emit then Γw.ofBool (digit (a.getD false) (b.getD false) carry) else readBackWrite c.output.read),
        idleDir c.input.read, direction left right (fun j => (c.work j).read), if emit then .right else idleDir c.output.read) := by
    simp only [machine, action, hs]
    rw [ite_eq_right hend]
    simp only [dataAction, hl, hr, read_symbol]
  rw [TM.step, ite_eq_right (by simp [machine, hs]), hδ]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · rfl
  · cases emit
    · rfl
    · simp only [↓reduceIte, Γw.ofBool_toΓ]

theorem end_step (left right flag : Fin w) (emit carry : Bool) (c : Cfg w (machine left right flag emit).Q)
    (hs : c.state = some carry) (hl : (c.work left).read = Γ.blank) (hr : (c.work right).read = Γ.blank) :
    (machine left right flag emit).step c = some
      ⟨none, transitionInput c.input, finishWork flag emit carry c.work, transitionTape c.output⟩ := by
  have hδ : (machine left right flag emit).δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      finishAction flag emit carry c.input.read (fun j => (c.work j).read) c.output.read := by
    simp [machine, action, hs, hl, hr]
  rw [TM.step, ite_eq_right (by simp [machine, hs]), hδ]
  unfold finishAction finishWork transitionInput transitionTape
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    by_cases he : j = flag ∧ emit = false <;> simp [he]
  · rfl

theorem data_other (left right j : Fin w) (work : Fin w → Tape)
    (hl : j ≠ left) (hr : j ≠ right) (hw : (work j).read ≠ Γ.start) : dataWork left right work j = work j := by
  change (work j).writeAndMove (readBackWrite (work j).read) _ = work j
  rw [writeAndMove_readBack _ hw]
  simp [direction, hl, hr, idleDir, hw, Tape.move]

theorem data_left (left right : Fin w) (work : Fin w → Tape) (a : Option Bool)
    (ha : (work left).read = symbol a) :
    dataWork left right work left = if a.isSome then (work left).move .right else work left := by
  have hw : (work left).read ≠ Γ.start := by cases a with
    | none => simp [ha, symbol]
    | some a => simpa only [ha, symbol] using Γ.ofBool_ne_start a
  change (work left).writeAndMove (readBackWrite (work left).read) _ = _
  rw [writeAndMove_readBack _ hw]
  cases a with
  | none => simp [direction, ha, symbol, Tape.move]
  | some a => simp [direction, ha, symbol, Γ.ofBool_ne_blank]

theorem data_right (left right : Fin w) (work : Fin w → Tape) (b : Option Bool)
    (hb : (work right).read = symbol b) :
    dataWork left right work right = if b.isSome then (work right).move .right else work right := by
  have hw : (work right).read ≠ Γ.start := by cases b with
    | none => simp [hb, symbol]
    | some b => simpa only [hb, symbol] using Γ.ofBool_ne_start b
  change (work right).writeAndMove (readBackWrite (work right).read) _ = _
  rw [writeAndMove_readBack _ hw]
  cases b with
  | none => simp [direction, hb, symbol, Tape.move]
  | some b => simp [direction, hb, symbol, Γ.ofBool_ne_blank]

theorem finish_other (flag j : Fin w) (emit carry : Bool) (work : Fin w → Tape)
    (hj : j ≠ flag) (hw : (work j).read ≠ Γ.start) : finishWork flag emit carry work j = work j := by
  simp only [finishWork, hj, false_and, ↓reduceIte]
  exact transitionTape_eq_self hw

theorem finish_emit (flag : Fin w) (carry : Bool) (work : Fin w → Tape) (hw : ∀ j, (work j).read ≠ Γ.start) :
    finishWork flag true carry work = work := by
  funext j
  simp only [finishWork, Bool.true_eq_false, and_false, ↓reduceIte]
  exact transitionTape_eq_self (hw j)

end JointThermoComplexity.Complexity.BinaryDifferenceStep

#print axioms JointThermoComplexity.Complexity.BinaryDifferenceStep.data_step
#print axioms JointThermoComplexity.Complexity.BinaryDifferenceStep.end_step
#print axioms JointThermoComplexity.Complexity.BinaryDifferenceStep.data_left
#print axioms JointThermoComplexity.Complexity.BinaryDifferenceStep.finish_emit
