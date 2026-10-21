module
public import proofs.JointThermoComplexity.Complexity.VariableOutput

set_option autoImplicit false
@[expose] public section

/-! Variable output restores every work tape, permitting an arbitrary surrounding predicate. -/

namespace JointThermoComplexity.Complexity.VariableFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax

variable {w arity : ℕ}

theorem hoareTime (fuel scratch : Fin w) (hne : fuel ≠ scratch) (idx : Fin arity)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (VariableOutput.machine fuel scratch).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg idx.val (work fuel) ∧ Register 0 (work scratch) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (Term.var idx).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ IsReg idx.val (work fuel) ∧ Register 0 (work scratch) ∧ R work)
      (VariableOutput.timeBound idx.val) := by
  rintro inp work out ⟨hc, hs, hf, hb, hr⟩
  let Frame : (Fin w → Tape) → Prop := fun work' => ∀ j, j ≠ fuel → j ≠ scratch → work' j = work j
  have hFrame : ∀ work' work'', (∀ j, j ≠ fuel → j ≠ scratch → work'' j = work' j) → Frame work' → Frame work'' := by
    intro work' work'' hw h j hjf hjs
    exact (hw j hjf hjs).trans (h j hjf hjs)
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdsafe, hdfuel, hdscratch, hdFrame⟩ :=
    VariableOutput.hoareTime fuel scratch hne idx before input emitted Frame hFrame inp work out
      ⟨hc, hs, hf, hb, fun _ _ _ => rfl⟩
  have hwork : d.work = work := by
    funext j
    by_cases hjf : j = fuel
    · subst j
      exact hdfuel.eq_regT.trans hf.eq_regT.symm
    · by_cases hjs : j = scratch
      · subst j
        exact (Tape.eq_init_move_right_of_hasBinaryString hdscratch.1 hdscratch.2).trans
          (Tape.eq_init_move_right_of_hasBinaryString hb.1 hb.2).symm
      · exact hdFrame j hjf hjs
  exact ⟨d, t, ht, hreach, hhalt, hdcur, hdsafe, hdfuel, hdscratch, by simpa only [hwork] using hr⟩

end JointThermoComplexity.Complexity.VariableFrame

#print axioms JointThermoComplexity.Complexity.VariableFrame.hoareTime
