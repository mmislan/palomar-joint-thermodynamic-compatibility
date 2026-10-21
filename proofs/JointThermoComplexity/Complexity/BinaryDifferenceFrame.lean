module
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceStep
public import proofs.JointThermoComplexity.Complexity.TapeSafety

set_option autoImplicit false
@[expose] public section

/-! Borrow-scan transitions preserve all operand contents and marker safety and expose the actual comparison flag. -/

namespace JointThermoComplexity.Complexity.BinaryDifferenceFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryDifferenceMachine BinaryDifferenceStep

variable {w : ℕ}

theorem data_cells (left right j : Fin w) (work : Fin w → Tape) (hw : (work j).read ≠ Γ.start) :
    (dataWork left right work j).cells = (work j).cells := by
  change ((work j).writeAndMove (readBackWrite (work j).read) _).cells = _
  rw [writeAndMove_readBack _ hw]
  exact Tape.move_cells _ _

theorem data_parked (left right : Fin w) (work : Fin w → Tape) (hs : ∀ j, Parked (work j)) :
    ∀ j, Parked (dataWork left right work j) := by
  intro j
  have hw := (hs j).read_ne_start
  have hh := (hs j).1
  refine ⟨?_, by simpa only [data_cells left right j work hw] using (hs j).2⟩
  by_cases hj : j = left ∨ j = right
  · change 1 ≤ ((work j).writeAndMove (readBackWrite (work j).read) _).head
    rw [writeAndMove_readBack _ hw]
    simp only [direction, hj, ↓reduceIte]
    by_cases hb : (work j).read = Γ.blank
    · simp only [hb, ↓reduceIte, Tape.move]
      exact hh
    · simp only [hb, ↓reduceIte, Tape.move]
      omega
  · have hl : j ≠ left := fun he => hj (Or.inl he)
    have hr : j ≠ right := fun he => hj (Or.inr he)
    rw [data_other left right j work hl hr hw]
    exact hh

theorem finish_compare (flag : Fin w) (carry : Bool) (work : Fin w → Tape) (hw : (work flag).read ≠ Γ.start) :
    finishWork flag false carry work flag = (work flag).write (Γ.ofBool carry) := by
  have hidle : idleDir (work flag).read = .stay := by cases hg : (work flag).read <;> simp_all [idleDir]
  cases carry <;> simp [finishWork, hidle, Γw.ofBool, Γ.ofBool, Tape.move]

theorem finish_compare_head (flag : Fin w) (carry : Bool) (work : Fin w → Tape) (hw : (work flag).read ≠ Γ.start) :
    (finishWork flag false carry work flag).head = (work flag).head := by
  rw [finish_compare flag carry work hw, Tape.write_head]

theorem finish_compare_read (flag : Fin w) (carry : Bool) (work : Fin w → Tape)
    (hw : (work flag).read ≠ Γ.start) (hh : (work flag).head = 1) :
    (finishWork flag false carry work flag).read = Γ.ofBool carry := by
  rw [finish_compare flag carry work hw]
  simp [Tape.read, Tape.write, hh]

theorem finish_compare_zero (flag : Fin w) (carry : Bool) (work : Fin w → Tape)
    (hw : (work flag).read ≠ Γ.start) (hz : (work flag).cells 0 = Γ.start) :
    (finishWork flag false carry work flag).cells 0 = Γ.start := by
  rw [finish_compare flag carry work hw]
  simpa only [Tape.move] using Tape.write_move_cell0 (Γ.ofBool carry) .stay hz

theorem finish_compare_parked (flag : Fin w) (carry : Bool) (work : Fin w → Tape)
    (hs : ∀ j, Parked (work j)) : ∀ j, Parked (finishWork flag false carry work j) := by
  intro j
  by_cases hj : j = flag
  · subst j
    have hw := (hs flag).read_ne_start
    refine ⟨by rw [finish_compare_head flag carry work hw]; exact (hs flag).1, ?_⟩
    rw [finish_compare flag carry work hw]
    simpa only [Tape.move] using TapeSafety.write_move (work flag) (Γ.ofBool carry) .stay (Γ.ofBool_ne_start carry) (hs flag).2
  · rw [finish_other flag j false carry work hj (hs j).read_ne_start]
    exact hs j

end JointThermoComplexity.Complexity.BinaryDifferenceFrame

#print axioms JointThermoComplexity.Complexity.BinaryDifferenceFrame.data_parked
#print axioms JointThermoComplexity.Complexity.BinaryDifferenceFrame.finish_compare_read
#print axioms JointThermoComplexity.Complexity.BinaryDifferenceFrame.finish_compare_parked
