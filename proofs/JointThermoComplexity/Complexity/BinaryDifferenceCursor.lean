module
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceFrame
public import proofs.JointThermoComplexity.Complexity.BinaryTape

set_option autoImplicit false
@[expose] public section

/-! Canonical raw operand cursors and their exact one-step advancement for a complete borrow scan. -/

namespace JointThermoComplexity.Complexity.BinaryDifferenceCursor
open _root_.Complexity
open _root_.Complexity.TM
open BinaryBorrow BinaryDifferenceMachine BinaryDifferenceStep BinaryDifferenceFrame

variable {w : ℕ}

def consumed (xs : List Bool) : List Bool := xs.head?.toList

theorem consumed_tail (xs : List Bool) : consumed xs ++ xs.tail = xs := by cases xs <;> rfl

theorem tail_width (xs ys : List Bool) (hne : ¬(xs = [] ∧ ys = [])) :
    max xs.tail.length ys.tail.length + 1 = max xs.length ys.length := by
  cases xs <;> cases ys <;> simp_all [BinaryDifference.max_succ]

theorem subtract_step (xs ys : List Bool) (carry : Bool) (hne : ¬(xs = [] ∧ ys = [])) :
    BinaryDifference.subtract xs ys carry =
      (digit (xs.head?.getD false) (ys.head?.getD false) carry ::
        (BinaryDifference.subtract xs.tail ys.tail (borrow (xs.head?.getD false) (ys.head?.getD false) carry)).1,
        (BinaryDifference.subtract xs.tail ys.tail (borrow (xs.head?.getD false) (ys.head?.getD false) carry)).2) := by
  cases xs <;> cases ys <;> simp_all [BinaryDifference.subtract]

structure Separate (left right flag : Fin w) : Prop where
  operands : left ≠ right
  flagLeft : flag ≠ left
  flagRight : flag ≠ right

structure Operand (before remaining : List Bool) (t : Tape) : Prop where
  content : t.HasBinaryContent (before ++ remaining)
  head : t.head = before.length + 1
  zero : t.cells 0 = Γ.start

theorem Operand.read {before xs : List Bool} {t : Tape} (h : Operand before xs t) : t.read = symbol xs.head? := by
  cases xs with
  | nil => exact BinaryTape.read_end before (by simpa only [List.append_nil] using h.content) h.head
  | cons a xs => exact BinaryTape.read_cons before xs a h.content h.head

theorem Operand.advance {before xs : List Bool} {t : Tape} (h : Operand before xs t) :
    Operand (before ++ consumed xs) xs.tail (if xs.head?.isSome then t.move .right else t) := by
  cases xs with
  | nil => simpa [consumed] using h
  | cons a xs =>
    change Operand (before ++ [a]) xs (t.move .right)
    refine ⟨?_, ?_, h.zero⟩
    · simpa only [List.append_assoc, List.singleton_append]
        using h.content.move .right
    · change t.head + 1 = (before ++ [a]).length + 1
      rw [h.head]
      simp only [List.length_append, List.length_singleton]

structure Ready (left right flag : Fin w) (px py xs ys emitted : List Bool) (c : Cfg w (Option Bool)) : Prop where
  left : Operand px xs (c.work left)
  right : Operand py ys (c.work right)
  safe : ∀ j, Parked (c.work j)
  flagHead : (c.work flag).head = 1
  inputRead : c.input.read ≠ Γ.start
  outputPrefix : c.output.HasBinaryPrefix emitted
  zero : c.output.cells 0 = Γ.start

def nextCfg (left right : Fin w) (emit carry : Bool) (xs ys : List Bool) (c : Cfg w (Option Bool)) : Cfg w (Option Bool) :=
  ⟨some (borrow (xs.head?.getD false) (ys.head?.getD false) carry), transitionInput c.input, dataWork left right c.work,
    if emit then c.output.writeAndMove (Γ.ofBool (digit (xs.head?.getD false) (ys.head?.getD false) carry)) .right else transitionTape c.output⟩

def nextEmitted (emit carry : Bool) (xs ys emitted : List Bool) : List Bool :=
  emitted ++ (if emit then [digit (xs.head?.getD false) (ys.head?.getD false) carry] else [])

theorem next_step (left right flag : Fin w) (emit carry : Bool) (px py xs ys emitted : List Bool)
    (c : Cfg w (Option Bool)) (hs : c.state = some carry) (hc : Ready left right flag px py xs ys emitted c)
    (hne : ¬(xs = [] ∧ ys = [])) :
    (machine left right flag emit).step c = some (nextCfg left right emit carry xs ys c) := by
  have hheads : xs.head? ≠ none ∨ ys.head? ≠ none := by cases xs <;> cases ys <;> simp_all
  exact data_step left right flag emit carry xs.head? ys.head? c hs hc.left.read hc.right.read hheads

theorem next_input (left right flag : Fin w) (emit carry : Bool) (px py xs ys emitted : List Bool)
    (c : Cfg w (Option Bool)) (hc : Ready left right flag px py xs ys emitted c) :
    (nextCfg left right emit carry xs ys c).input = c.input := transitionInput_eq_self hc.inputRead

theorem next_other (left right flag : Fin w) (emit carry : Bool) (px py xs ys emitted : List Bool)
    (c : Cfg w (Option Bool)) (hc : Ready left right flag px py xs ys emitted c)
    (j : Fin w) (hl : j ≠ left) (hr : j ≠ right) :
    (nextCfg left right emit carry xs ys c).work j = c.work j :=
  data_other left right j c.work hl hr (hc.safe j).read_ne_start

theorem next_ready (left right flag : Fin w) (sep : Separate left right flag) (emit carry : Bool)
    (px py xs ys emitted : List Bool) (c : Cfg w (Option Bool)) (hc : Ready left right flag px py xs ys emitted c) :
    Ready left right flag (px ++ consumed xs) (py ++ consumed ys) xs.tail ys.tail
      (nextEmitted emit carry xs ys emitted) (nextCfg left right emit carry xs ys c) := by
  have hl : Operand (px ++ consumed xs) xs.tail ((nextCfg left right emit carry xs ys c).work left) := by
    change Operand _ _ (dataWork left right c.work left)
    rw [data_left left right c.work xs.head? hc.left.read]
    exact hc.left.advance
  have hr : Operand (py ++ consumed ys) ys.tail ((nextCfg left right emit carry xs ys c).work right) := by
    change Operand _ _ (dataWork left right c.work right)
    rw [data_right left right c.work ys.head? hc.right.read]
    exact hc.right.advance
  have hflag := next_other left right flag emit carry px py xs ys emitted c hc flag sep.flagLeft sep.flagRight
  have hinput := next_input left right flag emit carry px py xs ys emitted c hc
  refine ⟨hl, hr, data_parked left right c.work hc.safe, by rw [hflag]; exact hc.flagHead,
    by rw [hinput]; exact hc.inputRead, ?_, ?_⟩
  · cases emit
    · have ho : transitionTape c.output = c.output := transitionTape_eq_self (by simp [hc.outputPrefix.read_blank])
      simpa only [nextCfg, nextEmitted, Bool.false_eq_true, ↓reduceIte, List.append_nil, ho] using hc.outputPrefix
    · exact Tape.hasBinaryPrefix_write_bit _ hc.outputPrefix
  · cases emit
    · have ho : transitionTape c.output = c.output := transitionTape_eq_self (by simp [hc.outputPrefix.read_blank])
      simpa only [nextCfg, Bool.false_eq_true, ↓reduceIte, ho] using hc.zero
    · exact Tape.hasBinaryPrefix_write_bit_cell0 _ hc.outputPrefix hc.zero

end JointThermoComplexity.Complexity.BinaryDifferenceCursor

#print axioms JointThermoComplexity.Complexity.BinaryDifferenceCursor.next_step
#print axioms JointThermoComplexity.Complexity.BinaryDifferenceCursor.next_ready
