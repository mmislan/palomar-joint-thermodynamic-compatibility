module
public import proofs.JointThermoComplexity.Complexity.MotifDirectionStep
public import proofs.JointThermoComplexity.Complexity.InvariantLoop
public import proofs.JointThermoComplexity.Complexity.MonomialRestore

set_option autoImplicit false
@[expose] public section

/-! Run a complete direction iteration under a displaced physical reaction-fuel head and restored logical metadata. -/

namespace JointThermoComplexity.Complexity.MotifDirectionFuelFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts MotifDirectionState MotifDirectionFrame InvariantLoop

variable {arity : ℕ}

theorem replace (m L idx : ℕ) (mask flags : List Bool) (i : ℕ)
    (R S : (Fin (m + 15) → Tape) → Prop) (r : Fin (m + 15)) (sep : BoxState.Separate m r)
    (work work' : Fin (m + 15) → Tape) (hw : ∀ j, j ≠ r → work' j = work j) (ht : Parked (work' r))
    (hr : R work → S work') (hp : State m L idx mask flags i R work) : State m L idx mask flags i S work' := by
  exact ⟨BoxState.replace m L idx R S r sep work work' hw ht hr hp.1,
    by rw [hw (buffer m 1) sep.loDen.symm]; exact hp.2.1,
    by rw [hw (buffer m 2) sep.hiNum.symm]; exact hp.2.2⟩

theorem hoareTime (m L v head : ℕ) (hh : 1 ≤ head) (r : Fin (m + 15)) (sep : BoxState.Separate m r)
    (ha : arity ≤ 4 * L) (idx : Fin arity) (mask flags : List Bool) (i : ℕ)
    (hm : mask.length ≤ L) (hf : flags.length ≤ L) (him : i < mask.length) (hif : i < flags.length)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (MotifDirectionStep.machine m).HoareTime
      (Frame r v head (fun inp work out => Cursor before input emitted inp work out ∧ State m L idx.val mask flags i R work))
      (Frame r v head (fun inp work out => Cursor before input
        (emitted ++ MotifDirectionClause.word mask[i] flags[i] idx) inp work out ∧
          State m L (idx.val + 1) mask flags (i + 1) R work)) (MotifDirectionStep.timeBound L) := by
  let T : (Fin (m + 15) → Tape) → Prop := fun work => R (restore work r v) ∧ work r = ⟨head, regCells v⟩
  have hT : ∀ work work', Unchanged m work work' → T work → T work' := by
    rintro work work' hw ⟨hr, hrfuel⟩
    refine ⟨hR _ _ ?_ hr, ?_⟩
    · intro j hmask hflag hsource
      by_cases he : j = r
      · subst j; simp only [restore, Function.update_self]
      · simp only [restore, Function.update_of_ne he]
        exact hw j hmask hflag hsource
    · rw [hw r sep.loDen sep.hiNum sep.source]
      exact hrfuel
  have hs := MotifDirectionStep.hoareTime m L ha idx mask flags i hm hf him hif before input emitted T hT
  intro inp work out hframe
  obtain ⟨hc, hp⟩ := hframe.invariant
  have hpark := MonomialRestore.current_fuel_parked r v head work hh hframe.fuel
  have hw : ∀ j, j ≠ r → work j = restore work r v j := by intro j hj; simp only [restore, Function.update_of_ne hj]
  have hc' := MonomialRestore.cursor_replace r (restore work r v) work hw hpark hc
  have hp' := replace m L idx.val mask flags i R T r sep (restore work r v) work hw hpark (fun hr => ⟨hr, hframe.fuel⟩) hp
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdp⟩ := hs inp work out ⟨hc', hp'⟩
  have hdT : T d.work := hdp.1.2.2.2.2
  have hwd : ∀ j, j ≠ r → restore d.work r v j = d.work j := by intro j hj; simp only [restore, Function.update_of_ne hj]
  have hpd : Parked (restore d.work r v r) := by simp only [restore, Function.update_self]; exact (reg_regT v).parked
  exact ⟨d, t, ht, hreach, hhalt, hdT.2, hdc.input_read, (fun j _ => (hdc.works j).1), hdc.output_read,
    MonomialRestore.cursor_replace r d.work (restore d.work r v) hwd hpd hdc,
    replace m L (idx.val + 1) mask flags (i + 1) T R r sep d.work (restore d.work r v) hwd hpd (fun ht => ht.1) hdp⟩

end JointThermoComplexity.Complexity.MotifDirectionFuelFrame

#print axioms JointThermoComplexity.Complexity.MotifDirectionFuelFrame.replace
#print axioms JointThermoComplexity.Complexity.MotifDirectionFuelFrame.hoareTime
