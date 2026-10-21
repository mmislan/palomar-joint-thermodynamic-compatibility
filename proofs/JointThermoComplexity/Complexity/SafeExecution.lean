module
public import proofs.JointThermoComplexity.Complexity.TapeSafety

set_option autoImplicit false
@[expose] public section

/-! Carry work-tape marker safety through any proved actual-machine execution. -/

namespace JointThermoComplexity.Complexity.SafeExecution
open _root_.Complexity
open _root_.Complexity.TM

variable {w : ℕ}

theorem hoareTime (tm : TM w) (pre post : _root_.Complexity.TM.TapePred w) (bound : ℕ)
    (h : tm.HoareTime pre post bound)
    (hheads : ∀ inp work out, post inp work out → ∀ j, 1 ≤ (work j).head) :
    tm.HoareTime
      (fun inp work out => pre inp work out ∧ ∀ j, Parked (work j))
      (fun inp work out => post inp work out ∧ ∀ j, Parked (work j)) bound := by
  rintro inp work out ⟨hp, hs⟩
  obtain ⟨d, t, ht, hr, hh, hpost⟩ := h inp work out hp
  exact ⟨d, t, ht, hr, hh, hpost, fun j =>
    ⟨hheads d.input d.work d.output hpost j, TapeSafety.work_reaches j hr (hs j).2⟩⟩

end JointThermoComplexity.Complexity.SafeExecution

#print axioms JointThermoComplexity.Complexity.SafeExecution.hoareTime
