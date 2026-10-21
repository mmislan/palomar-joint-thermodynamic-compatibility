module
public import proofs.JointThermoComplexity.Complexity.ValidityAnd
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Sticky validity as a composable cursor-preserving machine step. -/

namespace JointThermoComplexity.Complexity.AndCursor
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {n : ℕ}

theorem hoareTime (dst src : Fin n) (a b : Bool) (before input emitted : List Bool)
    (R : (Fin n → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ dst → work' j = work j) → R work → R work') :
    (ValidityAnd.machine dst src).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work dst).head = 1 ∧ (work dst).read = Γ.ofBool a ∧ (work src).read = Γ.ofBool b ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work dst).head = 1 ∧ (work dst).read = Γ.ofBool (a && b) ∧ R work) 1 := by
  rintro inp work out ⟨hc, hh, ha, hb, hr⟩
  obtain ⟨d, hreach, hhalt, hi, ho, hw, hdhead, hdread⟩ :=
    ValidityAnd.run dst src a b ⟨false, inp, work, out⟩ rfl hc.input_read hc.output_read
      (fun j => (hc.works j).1) hh ha hb
  have hcursor : Cursor before input emitted d.input d.work d.output := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hi] using hc.cells
    · simpa only [hi] using hc.head
    · intro j
      by_cases hj : j = dst
      · subst j
        refine ⟨?_, by rw [hdhead]⟩
        rw [hdread]
        exact Γ.ofBool_ne_start _
      · rw [hw j hj]
        exact hc.works j
    · simpa only [ho] using hc.tapePrefix
    · simpa only [ho] using hc.zero
  exact ⟨d, 1, le_rfl, hreach, hhalt, hcursor, hdhead, hdread, hR work d.work hw hr⟩

end JointThermoComplexity.Complexity.AndCursor

#print axioms JointThermoComplexity.Complexity.AndCursor.hoareTime
