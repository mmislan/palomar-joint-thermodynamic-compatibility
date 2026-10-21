module
public import proofs.JointThermoComplexity.Complexity.InvariantLoop
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! A generic exact-preservation traversal rule under a physical outer fuel head. -/

namespace JointThermoComplexity.Complexity.ReadOnlyFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop

variable {w : ℕ}

theorem hoareTime (tm : TM w) (outer : Fin w) (v head : ℕ) (hh : 1 ≤ head)
    (word before tail emitted : List Bool) (P : (Fin w → Tape) → Prop) (bound : ℕ)
    (hP : ∀ work work', (∀ j, j ≠ outer → work' j = work j) → P work → P work')
    (hcopy : ∀ S : (Fin w → Tape) → Tape → Prop, tm.HoareTime
      (fun inp work out => Cursor before (word ++ tail) emitted inp work out ∧ P work ∧ S work out)
      (fun inp work out => Cursor (before ++ word) tail emitted inp work out ∧ P work ∧ S work out) bound)
    (R : (Fin w → Tape) → Tape → Prop) :
    tm.HoareTime
      (Frame outer v head (fun inp work out => Cursor before (word ++ tail) emitted inp work out ∧ P work ∧ R work out))
      (Frame outer v head (fun inp work out => Cursor (before ++ word) tail emitted inp work out ∧ P work ∧ R work out)) bound := by
  intro inp work out hf
  obtain ⟨hc, hp, hr⟩ := hf.invariant
  have hcur : Cursor before (word ++ tail) emitted inp work out := by
    refine ⟨hc.cells, hc.head, ?_, hc.tapePrefix, hc.zero⟩
    intro j
    by_cases hj : j = outer
    · subst j
      rw [hf.fuel]
      exact ⟨regCells_ne_start hh, hh⟩
    · simpa only [restore, Function.update_of_ne hj] using hc.works j
  have hw : ∀ j, j ≠ outer → work j = restore work outer v j := by
    intro j hj; simp only [restore, Function.update_of_ne hj]
  have hphysical := hP (restore work outer v) work hw hp
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, _, hdwork, hdout⟩ :=
    hcopy (fun work' out' => work' = work ∧ out' = out) inp work out ⟨hcur, hphysical, rfl, rfl⟩
  have hlogical : Cursor (before ++ word) tail emitted d.input (restore d.work outer v) d.output := by
    refine ⟨hdcur.cells, hdcur.head, ?_, hdcur.tapePrefix, hdcur.zero⟩
    simpa only [hdwork] using hc.works
  refine ⟨d, t, ht, hreach, hhalt, ?_, hdcur.input_read, ?_, hdcur.output_read, hlogical, ?_, ?_⟩
  · simpa only [hdwork] using hf.fuel
  · intro j hj; simpa only [hdwork] using hf.readOthers j hj
  · simpa only [hdwork] using hp
  · simpa only [hdwork, hdout] using hr

end JointThermoComplexity.Complexity.ReadOnlyFrame

#print axioms JointThermoComplexity.Complexity.ReadOnlyFrame.hoareTime
