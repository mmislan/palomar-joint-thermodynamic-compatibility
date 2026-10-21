module
public import proofs.JointThermoComplexity.Complexity.CountOffset
public import proofs.JointThermoComplexity.Complexity.LoopCursor

set_option autoImplicit false
@[expose] public section

/-! Transport count-accumulator frames between physical loop heads and restored registers. -/

namespace JointThermoComplexity.Complexity.CountLoopFrame
open _root_.Complexity
open _root_.Complexity.TM
open CountAppend

variable {w : ℕ}

theorem oldWork_restore (work : Fin (w + 1) → Tape) (fuel : Fin w) (v : ℕ) :
    oldWork (InvariantLoop.restore work fuel.castSucc v) = Function.update (oldWork work) fuel (regTape v) := by
  funext j
  by_cases hj : j = fuel
  · subst j
    simp only [oldWork, InvariantLoop.restore, Function.update_self]
  · have hcast : j.castSucc ≠ fuel.castSucc := by
      intro he
      apply hj
      apply Fin.ext
      exact congrArg (fun z : Fin (w + 1) => z.val) he
    simp only [oldWork, InvariantLoop.restore, Function.update_of_ne hcast, Function.update_of_ne hj]

theorem destination_restore (work : Fin (w + 1) → Tape) (fuel : Fin w) (v : ℕ) :
    InvariantLoop.restore work fuel.castSucc v destination = work destination := by
  rw [InvariantLoop.restore, Function.update_of_ne (CountOffset.cast_ne_destination fuel).symm]

theorem physical_safe (work : Fin (w + 1) → Tape) (fuel : Fin w) (v head : ℕ)
    (hh : 1 ≤ head) (hf : work fuel.castSucc = ⟨head, regCells v⟩)
    (hs : ∀ j, Parked (InvariantLoop.restore work fuel.castSucc v j)) : ∀ j, Parked (work j) := by
  intro j
  by_cases hj : j = fuel.castSucc
  · subst j
    rw [hf]
    exact parked_regCells hh
  · have h := hs j
    rw [InvariantLoop.restore, Function.update_of_ne hj] at h
    exact h

end JointThermoComplexity.Complexity.CountLoopFrame

#print axioms JointThermoComplexity.Complexity.CountLoopFrame.oldWork_restore
