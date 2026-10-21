module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesStep
public import proofs.JointThermoComplexity.Complexity.InvariantLoop
public import proofs.JointThermoComplexity.Complexity.MonomialRestore

set_option autoImplicit false
@[expose] public section

/-! The actual species loop displaces copied fuel14 while the original species count remains at head one. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesFuelFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState InvariantLoop

def fuel (m : ℕ) : Fin (m + 22) := OuterFuelPorts.destination m 0

theorem ne_fuel (m : ℕ) (j : Fin (m + 22)) (hj : j.val ≤ 13 ∨ 16 ≤ j.val) : j ≠ fuel m := by
  intro he
  have hv := congrArg Fin.val he
  change j.val = 14 at hv
  omega

theorem fuel_eq (m : ℕ) (work work' : Fin (m + 22) → Tape) (hw : ProductionSpeciesFrame.Unchanged m work work') :
    work' (fuel m) = work (fuel m) :=
  ProductionSpeciesFrame.outside m work work' hw (fuel m) (Or.inr (Or.inr (by change 13 ≤ (14 : ℕ); omega)))

theorem replace (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount) (pos : ℕ)
    (R S : (Fin (m + 22) → Tape) → Prop) (work work' : Fin (m + 22) → Tape)
    (hw : ∀ j, j ≠ fuel m → work' j = work j) (ht : Parked (work' (fuel m)))
    (hr : R work → S work') (hp : State m input Q a pos R work) : State m input Q a pos S work' := by
  obtain ⟨ri, hri, idx, hidx, hdata, hi, hz, hm, hreact, hk, hraw, hf, hc, hR⟩ := hp
  have hx (j : Fin (m + 22)) (hj : j.val ≤ 13 ∨ 16 ≤ j.val) : work' j = work j := hw j (ne_fuel m j hj)
  have hs := MonomialRestore.safe_replace (fuel m) work work' hw hdata.safe ht
  have hu := OuterFuelCopyFrame.of_single m 0 work work' hw
  have hcopy := ProductionOperandData.outer_frame m input.length Q.speciesCount ri pos work work' hu
    (ProductionOperandData.of_state _ _ _ _ _ work hdata)
  exact ⟨ri, hri, idx, hidx, ProductionOperandData.to_state _ _ _ _ _ work' hs hcopy,
    by simpa only [hx (ProductionPorts.current (m + 2)) (Or.inl (by change (7 : ℕ) ≤ 13; omega))] using hi,
    by simpa only [hx (PowerPorts.scratch (m + 9)) (Or.inl (by change (5 : ℕ) ≤ 13; omega))] using hz,
    by simpa only [hx (MotifBufferPorts.buffer (m + 7) 0) (Or.inl (by change (2 : ℕ) ≤ 13; omega))] using hm,
    by simpa only [hx (MotifBufferPorts.buffer (m + 7) 1) (Or.inl (by change (3 : ℕ) ≤ 13; omega))] using hreact,
    OuterFuelCopyFrame.kept m input work work' hu hk,
    by simpa only [hx (CurrentPorts.raw (m + 7)) (Or.inr (by change 16 ≤ m + 21; omega))] using hraw,
    by simpa only [hx (MotifBufferPorts.buffer (m + 7) 2) (Or.inl (by change (4 : ℕ) ≤ 13; omega))] using hf,
    by simpa only [hx (ProductionPorts.core (m + 2)) (Or.inl (by change (13 : ℕ) ≤ 13; omega))] using hc, hr hR⟩

theorem hoareTime (m v head : ℕ) (hh : 1 ≤ head) (input : List Bool) (Q : NetworkCodec.Input)
    (hd : NetworkCodec.decode input = some Q) (a : Fin Q.coreCount) (s : Fin Q.speciesCount) (emitted : List Bool)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (ProductionSpeciesStep.machine m).HoareTime
      (Frame (fuel m) v head (fun inp work out => Cursor [] input emitted inp work out ∧ State m input Q a s.val R work))
      (Frame (fuel m) v head (fun inp work out => Cursor [] input (emitted ++ ProductionSpeciesStep.word Q a s) inp work out ∧
        State m input Q a (s.val + 1) R work)) (ProductionSpeciesStep.timeBound input.length) := by
  let T : (Fin (m + 22) → Tape) → Prop := fun work => R (restore work (fuel m) v) ∧ work (fuel m) = ⟨head, regCells v⟩
  have hT : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → T work → T work' := by
    rintro work work' hw ⟨hr, hf⟩
    refine ⟨hR _ _ ?_ hr, (fuel_eq m work work' hw).trans hf⟩
    intro j hm hreact hz hri hc hmag hl hright hsign hspecies
    by_cases he : j = fuel m
    · subst j; simp only [restore, Function.update_self]
    · simp only [restore, Function.update_of_ne he]
      exact hw j hm hreact hz hri hc hmag hl hright hsign hspecies
  have hs := ProductionSpeciesStep.hoareTime m input Q hd a s emitted T hT
  intro inp work out hframe
  obtain ⟨hc, hp⟩ := hframe.invariant
  have hpark := MonomialRestore.current_fuel_parked (fuel m) v head work hh hframe.fuel
  have hw : ∀ j, j ≠ fuel m → work j = restore work (fuel m) v j := by
    intro j hj; simp only [restore, Function.update_of_ne hj]
  have hc' := MonomialRestore.cursor_replace (fuel m) (restore work (fuel m) v) work hw hpark hc
  have hp' := replace m input Q a s.val R T (restore work (fuel m) v) work hw hpark (fun hr => ⟨hr, hframe.fuel⟩) hp
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdp⟩ := hs inp work out ⟨hc', hp'⟩
  have hdT : T d.work := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hrest⟩ := hdp
    exact hrest
  have hwd : ∀ j, j ≠ fuel m → restore d.work (fuel m) v j = d.work j := by
    intro j hj; simp only [restore, Function.update_of_ne hj]
  have hpd : Parked (restore d.work (fuel m) v (fuel m)) := by
    simp only [restore, Function.update_self]; exact (reg_regT v).parked
  exact ⟨d, t, ht, hreach, hhalt, hdT.2, hdc.input_read, (fun j _ => (hdc.works j).1), hdc.output_read,
    MonomialRestore.cursor_replace (fuel m) d.work (restore d.work (fuel m) v) hwd hpd hdc,
    replace m input Q a (s.val + 1) T R d.work (restore d.work (fuel m) v) hwd hpd (fun ht => ht.1) hdp⟩

end JointThermoComplexity.Complexity.ProductionSpeciesFuelFrame

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesFuelFrame.replace
#print axioms JointThermoComplexity.Complexity.ProductionSpeciesFuelFrame.hoareTime
