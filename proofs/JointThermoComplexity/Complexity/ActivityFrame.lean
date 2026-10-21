module
public import proofs.JointThermoComplexity.Complexity.ActivityStep

set_option autoImplicit false
@[expose] public section

/-! Emit an activity clause with the species fuel at its physical loop head and the invariant at cell one. -/

namespace JointThermoComplexity.Complexity.ActivityFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ActivityState InvariantLoop

theorem hoareTime {arity : ℕ} (m L v head : ℕ) (hh : 1 ≤ head) (r : Fin (m + 15))
    (hsource : r ≠ species (m + 1)) (hzero : r ≠ scratch (m + 2)) (ha : arity ≤ 4 * L) (idx : Fin arity)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → R work → R work') :
    (ActivityStep.machine m).HoareTime
      (Frame r v head (fun inp work out => Cursor before input emitted inp work out ∧ Ready m idx.val R work))
      (Frame r v head (fun inp work out => Cursor before input (emitted ++ ActivityStep.word idx) inp work out ∧
        Ready m (idx.val + 1) R work)) (ActivityStep.timeBound L) := by
  let T : (Fin (m + 15) → Tape) → Prop := fun work => R (restore work r v) ∧ work r = ⟨head, regCells v⟩
  have hT : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → T work → T work' := by
    rintro work work' hw ⟨hr, hf⟩
    refine ⟨hR _ _ ?_ hr, ?_⟩
    · intro j hj
      by_cases he : j = r
      · subst j; simp only [restore, Function.update_self]
      · simp only [restore, Function.update_of_ne he]
        exact hw j hj
    · rw [hw r hsource]
      exact hf
  have hs := ActivityStep.hoareTime m L ha idx before input emitted T hT
  intro inp work out hf
  obtain ⟨hc, hr⟩ := hf.invariant
  have hpark := MonomialRestore.current_fuel_parked r v head work hh hf.fuel
  have hw : ∀ j, j ≠ r → work j = restore work r v j := by
    intro j hj
    simp only [restore, Function.update_of_ne hj]
  have hc' := MonomialRestore.cursor_replace r (restore work r v) work hw hpark hc
  have hr' := ActivityState.replace m idx.val R T r hsource hzero (restore work r v) work hw hpark
    (fun hr => ⟨hr, hf.fuel⟩) hr
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdr⟩ := hs inp work out ⟨hc', hr'⟩
  have hdT : T d.work := hdr.2.2.2
  have hwd : ∀ j, j ≠ r → restore d.work r v j = d.work j := by
    intro j hj
    simp only [restore, Function.update_of_ne hj]
  have hpd : Parked (restore d.work r v r) := by
    simp only [restore, Function.update_self]
    exact (reg_regT v).parked
  exact ⟨d, t, ht, hreach, hhalt, hdT.2, hdc.input_read, (fun j _ => (hdc.works j).1), hdc.output_read,
    MonomialRestore.cursor_replace r d.work (restore d.work r v) hwd hpd hdc,
    ActivityState.replace m (idx.val + 1) T R r hsource hzero d.work (restore d.work r v) hwd hpd
      (fun ht => ht.1) hdr⟩

end JointThermoComplexity.Complexity.ActivityFrame

#print axioms JointThermoComplexity.Complexity.ActivityFrame.hoareTime
