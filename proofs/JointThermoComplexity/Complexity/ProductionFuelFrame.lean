module
public import proofs.JointThermoComplexity.Complexity.ProductionMaskInit
public import proofs.JointThermoComplexity.Complexity.InvariantLoop
public import proofs.JointThermoComplexity.Complexity.MonomialRestore

set_option autoImplicit false
@[expose] public section

/-! Run the production step with an actual displaced reaction-fuel head and a restored logical metadata view. -/

namespace JointThermoComplexity.Complexity.ProductionFuelFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionPorts ProductionReactionState InvariantLoop

def fuel (m : ℕ) : Fin (m + 20) := ReactionFuel.slot (m + 5)

theorem ne_fuel (m : ℕ) (j : Fin (m + 20)) (hj : j.val ≤ 12 ∨ j.val = m + 15) : j ≠ fuel m := by
  intro he
  have hv := congrArg Fin.val he
  change j.val = m + 16 at hv
  omega

theorem fuel_eq (m : ℕ) (work work' : Fin (m + 20) → Tape) (hw : Unchanged m work work') :
    work' (fuel m) = work (fuel m) := by
  apply hw (fuel m)
  · exact (ne_fuel m _ (Or.inl (by change (3 : ℕ) ≤ 12; omega))).symm
  · exact (ne_fuel m _ (Or.inl (by change (5 : ℕ) ≤ 12; omega))).symm
  · exact (ne_fuel m _ (Or.inl (by change (6 : ℕ) ≤ 12; omega))).symm
  · exact (ne_fuel m _ (Or.inl (by change (7 : ℕ) ≤ 12; omega))).symm
  · exact (ne_fuel m _ (Or.inl (by change (8 : ℕ) ≤ 12; omega))).symm
  · exact (ne_fuel m _ (Or.inl (by change (9 : ℕ) ≤ 12; omega))).symm
  · exact (ne_fuel m _ (Or.inl (by change (10 : ℕ) ≤ 12; omega))).symm
  · exact (ne_fuel m _ (Or.inl (by change (11 : ℕ) ≤ 12; omega))).symm

theorem replace (m L n ri si idx : ℕ) (mask : List Bool) (k : ℕ)
    (R S : (Fin (m + 20) → Tape) → Prop) (work work' : Fin (m + 20) → Tape)
    (hw : ∀ j, j ≠ fuel m → work' j = work j) (ht : Parked (work' (fuel m)))
    (hr : R work → S work') (hp : State m L n ri si idx mask k R work) : State m L n ri si idx mask k S work' := by
  have hx (j : Fin (m + 20)) (hj : j.val ≤ 12 ∨ j.val = m + 15) : work' j = work j := hw j (ne_fuel m j hj)
  have hs := MonomialRestore.safe_replace (fuel m) work work' hw hp.1.safe ht
  have hstate : ProductionOperandLoad.State m L n ri si work' :=
    ⟨hs, by simpa only [hx (left m) (Or.inl (by change (9 : ℕ) ≤ 12; omega))] using hp.1.productReusable,
      by simpa only [hx (right m) (Or.inl (by change (10 : ℕ) ≤ 12; omega))] using hp.1.reactantReusable,
      by simpa only [hx (magnitude m) (Or.inl (by change (8 : ℕ) ≤ 12; omega))] using hp.1.magnitudeReusable,
      by simpa only [hx (sign m) (Or.inl (by change (11 : ℕ) ≤ 12; omega))] using hp.1.signHead,
      by simpa only [hx (species m) (Or.inl (by change (12 : ℕ) ≤ 12; omega))] using hp.1.speciesPosition,
      by simpa only [hx (count m) (Or.inr rfl)] using hp.1.speciesCount,
      by simpa only [hx (reaction m) (Or.inl (by change (6 : ℕ) ≤ 12; omega))] using hp.1.reactionPosition⟩
  exact ⟨hstate, by simpa only [hx (current m) (Or.inl (by change (7 : ℕ) ≤ 12; omega))] using hp.2.1,
    by simpa only [hx (PowerPorts.scratch (m + 7)) (Or.inl (by change (5 : ℕ) ≤ 12; omega))] using hp.2.2.1,
    by simpa only [hx (MotifBufferPorts.buffer (m + 5) 1) (Or.inl (by change (3 : ℕ) ≤ 12; omega))] using hp.2.2.2.1,
    hr hp.2.2.2.2⟩

theorem hoareTime (m v head : ℕ) (hh : 1 ≤ head) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (i : Fin Q.reactionCount) (s : Fin Q.speciesCount) (mask : List Bool) (him : i.val < mask.length)
    (emitted : List Bool) (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (ProductionReactionStep.machine m).HoareTime
      (Frame (fuel m) v head (fun inp work out => Cursor [] input emitted inp work out ∧
        State m input.length Q.speciesCount i.val s.val (NetworkMembership.currentIndex Q.network i).val mask i.val R work))
      (Frame (fuel m) v head (fun inp work out => Cursor [] input (emitted ++ ProductionReactionStep.word Q i s mask[i.val]) inp work out ∧
        State m input.length Q.speciesCount (i.val + 1) s.val ((NetworkMembership.currentIndex Q.network i).val + 1) mask (i.val + 1) R work))
      (ProductionReactionStep.timeBound input.length) := by
  let T : (Fin (m + 20) → Tape) → Prop := fun work => R (restore work (fuel m) v) ∧ work (fuel m) = ⟨head, regCells v⟩
  have hT : ∀ work work', Unchanged m work work' → T work → T work' := by
    rintro work work' hw ⟨hr, hf⟩
    refine ⟨hR _ _ ?_ hr, (fuel_eq m work work' hw).trans hf⟩
    intro j hm hz hri hc hmag hl hright hsign
    by_cases he : j = fuel m
    · subst j; simp only [restore, Function.update_self]
    · simp only [restore, Function.update_of_ne he]
      exact hw j hm hz hri hc hmag hl hright hsign
  have hs := ProductionReactionStep.hoareTime m input Q hd i s mask him emitted T hT
  intro inp work out hframe
  obtain ⟨hc, hp⟩ := hframe.invariant
  have hpark := MonomialRestore.current_fuel_parked (fuel m) v head work hh hframe.fuel
  have hw : ∀ j, j ≠ fuel m → work j = restore work (fuel m) v j := by
    intro j hj; simp only [restore, Function.update_of_ne hj]
  have hc' := MonomialRestore.cursor_replace (fuel m) (restore work (fuel m) v) work hw hpark hc
  have hp' := replace m input.length Q.speciesCount i.val s.val (NetworkMembership.currentIndex Q.network i).val mask i.val
    R T (restore work (fuel m) v) work hw hpark (fun hr => ⟨hr, hframe.fuel⟩) hp
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdp⟩ := hs inp work out ⟨hc', hp'⟩
  have hdT : T d.work := hdp.2.2.2.2
  have hwd : ∀ j, j ≠ fuel m → restore d.work (fuel m) v j = d.work j := by
    intro j hj; simp only [restore, Function.update_of_ne hj]
  have hpd : Parked (restore d.work (fuel m) v (fuel m)) := by
    simp only [restore, Function.update_self]; exact (reg_regT v).parked
  exact ⟨d, t, ht, hreach, hhalt, hdT.2, hdc.input_read, (fun j _ => (hdc.works j).1), hdc.output_read,
    MonomialRestore.cursor_replace (fuel m) d.work (restore d.work (fuel m) v) hwd hpd hdc,
    replace m input.length Q.speciesCount (i.val + 1) s.val ((NetworkMembership.currentIndex Q.network i).val + 1) mask (i.val + 1)
      T R d.work (restore d.work (fuel m) v) hwd hpd (fun ht => ht.1) hdp⟩

end JointThermoComplexity.Complexity.ProductionFuelFrame

#print axioms JointThermoComplexity.Complexity.ProductionFuelFrame.replace
#print axioms JointThermoComplexity.Complexity.ProductionFuelFrame.hoareTime
