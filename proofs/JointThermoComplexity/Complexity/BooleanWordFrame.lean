module
public import proofs.JointThermoComplexity.Complexity.BooleanWordSkip

set_option autoImplicit false
@[expose] public section

/-! A read-only word traversal inside another count-controlled loop. -/

namespace JointThermoComplexity.Complexity.BooleanWordFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop

variable {w : ℕ}

theorem hoareTime (outer inner : Fin w) (hne : inner ≠ outer) (v head : ℕ) (hh : 1 ≤ head)
    (bits before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (BooleanWordSkip.machine inner).HoareTime
      (Frame outer v head (fun inp work out => Cursor before (bits ++ tail) emitted inp work out ∧
        IsReg bits.length (work inner) ∧ R work out))
      (Frame outer v head (fun inp work out => Cursor (before ++ bits) tail emitted inp work out ∧
        IsReg bits.length (work inner) ∧ R work out)) (4 * bits.length + 2) := by
  intro inp work out hf
  obtain ⟨hc, hr, hp⟩ := hf.invariant
  have hcur : Cursor before (bits ++ tail) emitted inp work out := by
    refine ⟨hc.cells, hc.head, ?_, hc.tapePrefix, hc.zero⟩
    intro j
    by_cases hj : j = outer
    · subst j
      rw [hf.fuel]
      exact ⟨regCells_ne_start hh, hh⟩
    · simpa only [restore, Function.update_of_ne hj] using hc.works j
  have hreg : IsReg bits.length (work inner) := by
    simpa only [restore, Function.update_of_ne hne] using hr
  have hs := BooleanWordSkip.hoareTime inner bits before tail emitted
    (fun work' out' => work' = work ∧ out' = out)
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, _, hdwork, hdout⟩ := hs inp work out ⟨hcur, hreg, rfl, rfl⟩
  have hlogical : Cursor (before ++ bits) tail emitted d.input (restore d.work outer v) d.output := by
    refine ⟨hdcur.cells, hdcur.head, ?_, hdcur.tapePrefix, hdcur.zero⟩
    simpa only [hdwork] using hc.works
  refine ⟨d, t, ht, hreach, hhalt, ?_, hdcur.input_read, ?_, hdcur.output_read, hlogical, ?_, ?_⟩
  · simpa only [hdwork] using hf.fuel
  · intro j hj
    simpa only [hdwork] using hf.readOthers j hj
  · simpa only [hdwork] using hr
  · simpa only [hdwork, hdout] using hp

end JointThermoComplexity.Complexity.BooleanWordFrame

#print axioms JointThermoComplexity.Complexity.BooleanWordFrame.hoareTime
