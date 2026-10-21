module
public import proofs.JointThermoComplexity.Complexity.BinaryTrimMachine

set_option autoImplicit false
@[expose] public section

/-! Exact work-tape edits and surrounding-tape frames for backward binary normalization. -/

namespace JointThermoComplexity.Complexity.BinaryTrimStep
open _root_.Complexity
open _root_.Complexity.TM
open BinaryTrimMachine

variable {w : ℕ}

theorem other (idx j : Fin w) (erase : Bool) (dir : Dir3) (work : Fin w → Tape)
    (hj : j ≠ idx) (hw : (work j).read ≠ Γ.start) : workUpdate idx erase dir work j = work j := by
  have hidle : idleDir (work j).read = .stay := by cases hr : (work j).read <;> simp_all [idleDir]
  simp only [workUpdate, hj, false_and, ↓reduceIte, workDir, hw, hidle]
  rw [writeAndMove_readBack _ hw]
  rfl

theorem move_selected (idx : Fin w) (dir : Dir3) (work : Fin w → Tape)
    (hw : (work idx).read ≠ Γ.start) : workUpdate idx false dir work idx = (work idx).move dir := by
  simp only [workUpdate, Bool.false_eq_true, and_false, ↓reduceIte, workDir, hw]
  exact writeAndMove_readBack _ hw dir

theorem erase_selected (idx : Fin w) (work : Fin w → Tape) (hr : (work idx).read = Γ.zero) :
    workUpdate idx true .left work idx = (work idx).writeAndMove Γ.blank .left := by
  simp [workUpdate, workDir, hr]

theorem marker_selected (idx : Fin w) (work : Fin w → Tape) (hh : (work idx).head = 0)
    (hz : (work idx).cells 0 = Γ.start) : workUpdate idx false .right work idx = (work idx).move .right := by
  have hr : (work idx).read = Γ.start := by rw [Tape.read, hh, hz]
  simp [workUpdate, workDir, hr]
  unfold Tape.writeAndMove
  rw [Tape.write, ite_eq_left hh]

theorem cfg_input (idx : Fin w) (q : Option Bool) (erase : Bool) (dir : Dir3)
    (c : Cfg w (Option Bool)) (hi : c.input.read ≠ Γ.start) :
    (cfg idx q erase dir c).input = c.input := transitionInput_eq_self hi

theorem cfg_output (idx : Fin w) (q : Option Bool) (erase : Bool) (dir : Dir3)
    (c : Cfg w (Option Bool)) (ho : c.output.read ≠ Γ.start) :
    (cfg idx q erase dir c).output = c.output := transitionTape_eq_self ho

theorem cfg_other (idx j : Fin w) (q : Option Bool) (erase : Bool) (dir : Dir3)
    (c : Cfg w (Option Bool)) (hj : j ≠ idx) (hw : (c.work j).read ≠ Γ.start) :
    (cfg idx q erase dir c).work j = c.work j := other idx j erase dir c.work hj hw

end JointThermoComplexity.Complexity.BinaryTrimStep

#print axioms JointThermoComplexity.Complexity.BinaryTrimStep.other
#print axioms JointThermoComplexity.Complexity.BinaryTrimStep.erase_selected
#print axioms JointThermoComplexity.Complexity.BinaryTrimStep.marker_selected
