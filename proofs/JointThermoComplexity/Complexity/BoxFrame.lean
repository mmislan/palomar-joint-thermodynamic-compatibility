module
public import proofs.JointThermoComplexity.Complexity.BoxStep

set_option autoImplicit false
@[expose] public section

/-! Transfer a box step between the physical counting head and the invariant's restored metadata view. -/

namespace JointThermoComplexity.Complexity.BoxFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts BoxState InvariantLoop NetworkData

theorem hoareTime {arity : ℕ} (m L v head : ℕ) (hh : 1 ≤ head) (r : Fin (m + 15))
    (sep : Separate m r) (ha : arity ≤ 4 * L) (box : Option ClosedBox)
    (hsize : BoxOptionalRuntime.Bounded L box) (idx : Fin arity) (before tail emitted : List Bool)
    (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (BoxStep.machine m).HoareTime
      (Frame r v head (fun inp work out => Cursor before ((FiniteCodec.optional DataCodec.box).code box ++ tail) emitted inp work out ∧
        Ready m L idx.val R work))
      (Frame r v head (fun inp work out => Cursor (before ++ (FiniteCodec.optional DataCodec.box).code box) tail
        (emitted ++ BoxStep.word box idx) inp work out ∧ Ready m L (idx.val + 1) R work)) (BoxStep.timeBound L) := by
  let T : (Fin (m + 15) → Tape) → Prop := fun work => R (restore work r v) ∧ work r = ⟨head, regCells v⟩
  have hT : ∀ work work', Unchanged m work work' → T work → T work' := by
    rintro work work' hw ⟨hr, hf⟩
    refine ⟨hR _ _ ?_ hr, ?_⟩
    · intro j ha hb hc hd hs
      by_cases he : j = r
      · subst j; simp only [restore, Function.update_self]
      · simp only [restore, Function.update_of_ne he]
        exact hw j ha hb hc hd hs
    · rw [hw r sep.loNum sep.loDen sep.hiNum sep.hiDen sep.source]
      exact hf
  have hs := BoxStep.hoareTime m L ha box hsize idx before tail emitted T hT
  intro inp work out hf
  obtain ⟨hc, hr⟩ := hf.invariant
  have hpark := MonomialRestore.current_fuel_parked r v head work hh hf.fuel
  have hw : ∀ j, j ≠ r → work j = restore work r v j := by
    intro j hj; simp only [restore, Function.update_of_ne hj]
  have hc' := MonomialRestore.cursor_replace r (restore work r v) work hw hpark hc
  have hr' := BoxState.replace m L idx.val R T r sep (restore work r v) work hw hpark
    (fun hr => ⟨hr, hf.fuel⟩) hr
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdr⟩ := hs inp work out ⟨hc', hr'⟩
  have hdT : T d.work := hdr.2.2.2.2
  have hwd : ∀ j, j ≠ r → restore d.work r v j = d.work j := by
    intro j hj; simp only [restore, Function.update_of_ne hj]
  have hpd : Parked (restore d.work r v r) := by
    simp only [restore, Function.update_self]
    exact (reg_regT v).parked
  exact ⟨d, t, ht, hreach, hhalt, hdT.2, hdc.input_read, (fun j _ => (hdc.works j).1), hdc.output_read,
    MonomialRestore.cursor_replace r d.work (restore d.work r v) hwd hpd hdc,
    BoxState.replace m L (idx.val + 1) T R r sep d.work (restore d.work r v) hwd hpd (fun ht => ht.1) hdr⟩

end JointThermoComplexity.Complexity.BoxFrame

#print axioms JointThermoComplexity.Complexity.BoxFrame.hoareTime
