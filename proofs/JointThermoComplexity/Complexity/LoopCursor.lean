module
public import proofs.JointThermoComplexity.Complexity.InvariantLoop
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Cursor transport between physical fuel heads and parked invariant views. -/

namespace JointThermoComplexity.Complexity.LoopCursor
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {n : ℕ} {before input emitted : List Bool} {inp out : Tape} {work : Fin n → Tape}

theorem restore (hc : Cursor before input emitted inp work out) (r : Fin n) (v : ℕ) :
    Cursor before input emitted inp (InvariantLoop.restore work r v) out := by
  refine ⟨hc.cells, hc.head, ?_, hc.tapePrefix, hc.zero⟩
  intro j
  by_cases hj : j = r
  · subst j
    rw [InvariantLoop.restore, Function.update_self]
    exact ⟨(reg_regT v).parked.read_ne_start, (reg_regT v).parked.1⟩
  · rw [InvariantLoop.restore, Function.update_of_ne hj]
    exact hc.works j

theorem physical (r : Fin n) (v : ℕ)
    (hc : Cursor before input emitted inp (InvariantLoop.restore work r v) out)
    (hr : (work r).read ≠ Γ.start ∧ 1 ≤ (work r).head) :
    Cursor before input emitted inp work out := by
  refine ⟨hc.cells, hc.head, ?_, hc.tapePrefix, hc.zero⟩
  intro j
  by_cases hj : j = r
  · subst j
    exact hr
  · have h := hc.works j
    rw [InvariantLoop.restore, Function.update_of_ne hj] at h
    exact h

end JointThermoComplexity.Complexity.LoopCursor

#print axioms JointThermoComplexity.Complexity.LoopCursor.physical
