module
public import proofs.JointThermoComplexity.Complexity.MotifCoreStep
public import proofs.JointThermoComplexity.Complexity.InvariantLoop

set_option autoImplicit false
@[expose] public section

/-! Complete core processing runs under displaced copied core fuel15, retaining the distinct copied species fuel14. -/

namespace JointThermoComplexity.Complexity.MotifCoreFuelFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifCoreState InvariantLoop

def fuel (m : ℕ) : Fin (m + 22) := OuterFuelPorts.destination m 1

theorem species_ne_fuel (m : ℕ) : OuterFuelPorts.destination m 0 ≠ fuel m := by
  intro he
  have hv := congrArg Fin.val he
  change (14 : ℕ) = 15 at hv
  omega

theorem fuel_eq (m : ℕ) (work work' : Fin (m + 22) → Tape) (hw : MotifCompleteFrame.Unchanged m work work') :
    work' (fuel m) = work (fuel m) := hw (fuel m) (Or.inr (by change 14 ≤ (15 : ℕ); omega))

theorem replace (m ci : ℕ) (input : List Bool) (Q : NetworkCodec.Input)
    (R S : (Fin (m + 22) → Tape) → Prop) (work work' : Fin (m + 22) → Tape)
    (hw : ∀ j, j ≠ fuel m → work' j = work j) (ht : Parked (work' (fuel m)))
    (hr : R work → S work') (hp : State m input Q ci R work) : State m input Q ci S work' := by
  obtain ⟨hready, ri, hdata, hR⟩ := hp
  have hu := OuterFuelCopyFrame.of_single m 1 work work' hw
  exact ⟨OuterFuelCopyFrame.prepared_replace m input Q 1 work work' hw ht hready,
    ri, OuterProductionResources.outer_frame m input.length Q.speciesCount ri 0 ci work work' hu hdata, hr hR⟩

theorem hoareTime (m v head : ℕ) (hh : 1 ≤ head) (input : List Bool) (Q : NetworkCodec.Input)
    (hd : NetworkCodec.decode input = some Q) (a : Fin Q.coreCount) (emitted : List Bool)
    (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', MotifCompleteFrame.Unchanged m work work' → R work → R work') :
    (MotifCoreStep.machine m).HoareTime
      (Frame (fuel m) v head (fun inp work out => Cursor [] input emitted inp work out ∧ State m input Q a.val R work ∧
        IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0))))
      (Frame (fuel m) v head (fun inp work out => Cursor [] input (emitted ++ MotifCoreStep.word Q a) inp work out ∧
        State m input Q (a.val + 1) R work ∧ IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0))))
      (MotifCoreStep.timeBound input.length) := by
  let T : (Fin (m + 22) → Tape) → Prop := fun work => R (restore work (fuel m) v) ∧ work (fuel m) = ⟨head, regCells v⟩
  have hT : ∀ work work', MotifCompleteFrame.Unchanged m work work' → T work → T work' := by
    rintro work work' hw ⟨hr, hf⟩
    refine ⟨hR _ _ ?_ hr, (fuel_eq m work work' hw).trans hf⟩
    intro j hj
    by_cases he : j = fuel m
    · subst j; simp only [restore, Function.update_self]
    · simp only [restore, Function.update_of_ne he]
      exact hw j hj
  have hs := MotifCoreStep.hoareTime m input Q hd a emitted T hT
  intro inp work out hframe
  obtain ⟨hc, hp, hspecies⟩ := hframe.invariant
  have hpark := MonomialRestore.current_fuel_parked (fuel m) v head work hh hframe.fuel
  have hw : ∀ j, j ≠ fuel m → work j = restore work (fuel m) v j := by
    intro j hj; simp only [restore, Function.update_of_ne hj]
  have hc' := MonomialRestore.cursor_replace (fuel m) (restore work (fuel m) v) work hw hpark hc
  have hp' := replace m a.val input Q R T (restore work (fuel m) v) work hw hpark (fun hr => ⟨hr, hframe.fuel⟩) hp
  have hspecies' : IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) := by
    simpa only [restore, Function.update_of_ne (species_ne_fuel m)] using hspecies
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdp, hdspecies⟩ := hs inp work out ⟨hc', hp', hspecies'⟩
  have hdT : T d.work := by
    obtain ⟨_, _, _, hr⟩ := hdp
    exact hr
  have hwd : ∀ j, j ≠ fuel m → restore d.work (fuel m) v j = d.work j := by
    intro j hj; simp only [restore, Function.update_of_ne hj]
  have hpd : Parked (restore d.work (fuel m) v (fuel m)) := by
    simp only [restore, Function.update_self]; exact (reg_regT v).parked
  exact ⟨d, t, ht, hreach, hhalt, hdT.2, hdc.input_read, (fun j _ => (hdc.works j).1), hdc.output_read,
    MonomialRestore.cursor_replace (fuel m) d.work (restore d.work (fuel m) v) hwd hpd hdc,
    replace m (a.val + 1) input Q T R d.work (restore d.work (fuel m) v) hwd hpd (fun ht => ht.1) hdp,
    by simpa only [restore, Function.update_of_ne (species_ne_fuel m)] using hdspecies⟩

end JointThermoComplexity.Complexity.MotifCoreFuelFrame

#print axioms JointThermoComplexity.Complexity.MotifCoreFuelFrame.replace
#print axioms JointThermoComplexity.Complexity.MotifCoreFuelFrame.hoareTime
