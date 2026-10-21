module
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-!
# Work-tape marker safety for framed emission

The preservation argument adapts the output-tape argument in
Complexitylib.Models.TuringMachine.Internal, copyright (c) 2025 Samuel
Schlesinger, released under Apache 2.0; the retained license is in
third_party/complexitylib/LICENSE. The adopted source is unchanged.
-/

namespace JointThermoComplexity.Complexity.TapeSafety
open _root_.Complexity
open _root_.Complexity.TM

variable {w : ℕ}

theorem write_move (t : Tape) (s : Γ) (dir : Dir3) (hs : s ≠ Γ.start)
    (h : ∀ j, 1 ≤ j → t.cells j ≠ Γ.start) :
    ∀ j, 1 ≤ j → ((t.write s).move dir).cells j ≠ Γ.start := by
  intro j hj
  rw [Tape.move_cells]
  simp only [Tape.write]
  split
  · exact h j hj
  · simp only [Function.update]
    split
    · next he => subst he; exact hs
    · exact h j hj

theorem work_step {tm : TM w} {c d : Cfg w tm.Q} (idx : Fin w)
    (hs : tm.step c = some d) (h : ∀ j, 1 ≤ j → (c.work idx).cells j ≠ Γ.start) :
    ∀ j, 1 ≤ j → (d.work idx).cells j ≠ Γ.start := by
  have hne := state_ne_qhalt_of_step hs
  simp only [TM.step, hne, ↓reduceIte, Option.some.injEq] at hs
  subst hs
  exact write_move _ _ _ (Γw.toΓ_ne_start _) h

theorem work_reaches {tm : TM w} {c d : Cfg w tm.Q} {t : ℕ} (idx : Fin w)
    (hr : tm.reachesIn t c d) (h : ∀ j, 1 ≤ j → (c.work idx).cells j ≠ Γ.start) :
    ∀ j, 1 ≤ j → (d.work idx).cells j ≠ Γ.start := by
  induction hr with
  | zero => exact h
  | step hs _ ih => exact ih (work_step idx hs h)

theorem fresh_work_parked {tm : TM w} {input : List Bool} {d : Cfg w tm.Q} {t : ℕ}
    (hr : tm.reachesIn t (tm.initCfg input) d) (idx : Fin w) (hh : 1 ≤ (d.work idx).head) :
    Parked (d.work idx) :=
  ⟨hh, work_reaches idx hr Tape.init_nil_cells_ne_start⟩

end JointThermoComplexity.Complexity.TapeSafety

#print axioms JointThermoComplexity.Complexity.TapeSafety.fresh_work_parked
