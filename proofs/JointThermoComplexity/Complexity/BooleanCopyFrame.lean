module
public import proofs.JointThermoComplexity.Complexity.BooleanCopy
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! Copy an actual input bit while the outer count head is displaced from its logical register view. -/

namespace JointThermoComplexity.Complexity.BooleanCopyFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt InvariantLoop

variable {w : ℕ}

theorem hoareTime (r : Fin w) (v head : ℕ) (hh : 1 ≤ head) (bit : Bool)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (BooleanCopy.machine (w := w)).HoareTime
      (Frame r v head (fun inp work out => Cursor before (bit :: tail) emitted inp work out ∧ R work))
      (Frame r v head (fun inp work out => Cursor (before ++ [bit]) tail (emitted ++ [bit]) inp work out ∧ R work)) 1 := by
  intro inp work out hf
  obtain ⟨hc, hr⟩ := hf.invariant
  have hcur : Cursor before (bit :: tail) emitted inp work out := by
    refine ⟨hc.cells, hc.head, ?_, hc.tapePrefix, hc.zero⟩
    intro j
    by_cases hj : j = r
    · subst j
      rw [hf.fuel]
      exact ⟨regCells_ne_start hh, hh⟩
    · simpa only [restore, Function.update_of_ne hj] using hc.works j
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdw⟩ :=
    BooleanCopy.hoareTime bit before tail emitted (fun work' => work' = work) inp work out ⟨hcur, rfl⟩
  have hlogical : Cursor (before ++ [bit]) tail (emitted ++ [bit]) d.input (restore d.work r v) d.output := by
    refine ⟨hdc.cells, hdc.head, ?_, hdc.tapePrefix, hdc.zero⟩
    simpa only [hdw] using hc.works
  refine ⟨d, t, ht, hreach, hhalt, ?_, hdc.input_read, ?_, hdc.output_read, hlogical, ?_⟩
  · simpa only [hdw] using hf.fuel
  · intro j hj
    simpa only [hdw] using hf.readOthers j hj
  · simpa only [hdw] using hr

end JointThermoComplexity.Complexity.BooleanCopyFrame

#print axioms JointThermoComplexity.Complexity.BooleanCopyFrame.hoareTime
