module
public import proofs.JointThermoComplexity.Complexity.CurrentStep
public import proofs.JointThermoComplexity.Complexity.CurrentRestore

set_option autoImplicit false
@[expose] public section

/-! The current-record body executes with the actual positive outer-fuel head and its logical restored invariant. -/

namespace JointThermoComplexity.Complexity.CurrentFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts CurrentReady InvariantLoop

theorem hoareTime {n arity : ℕ} (m L count v head : ℕ) (hh : 1 ≤ head)
    (r : Fin (m + 15)) (sep : ReactionFuel.Separate m r) (hraw : r ≠ raw m)
    (q : ReactionCircuit.Reaction n) (current result : Fin arity)
    (ha : arity ≤ 4 * L) (hn : n ≤ L) (hlen : ((DataCodec.reaction n).code q).length ≤ L)
    (hresult : result.val + 1 = count + ExactGateCount.reactionCost q)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ raw m → j ≠ previous (m + 1) → j ≠ species (m + 1) →
      work' j = work j) → R work → R work') :
    (CurrentStep.machine m).HoareTime
      (Frame r v head (fun inp work out => Cursor before ((DataCodec.reaction n).code q ++ tail) emitted inp work out ∧
        Ready m L count current.val n R work))
      (Frame r v head (fun inp work out => Cursor (before ++ (DataCodec.reaction n).code q) tail
        (emitted ++ CurrentRecord.word q current result) inp work out ∧
        Ready m L (count + ExactGateCount.reactionCost q) (current.val + 1) n R work)) (CurrentStep.timeBound L) := by
  let T : (Fin (m + 15) → Tape) → Prop := fun work => R (restore work r v) ∧ work r = ⟨head, regCells v⟩
  have hT : ∀ work work', (∀ j, j ≠ raw m → j ≠ previous (m + 1) → j ≠ species (m + 1) →
      work' j = work j) → T work → T work' := by
    rintro work work' hw ⟨hr, hf⟩
    refine ⟨hR _ _ ?_ hr, ?_⟩
    · intro j hraw hprev hcurrent
      by_cases hj : j = r
      · subst j; simp only [restore, Function.update_self]
      · simp only [restore, Function.update_of_ne hj]
        exact hw j hraw hprev hcurrent
    · rw [hw r hraw sep.previous sep.species]
      exact hf
  have hstep := CurrentStep.hoareTime m L count q current result ha hn hlen hresult before tail emitted T hT
  intro inp work out hf
  obtain ⟨hc, hr⟩ := hf.invariant
  have hpark := MonomialRestore.current_fuel_parked r v head work hh hf.fuel
  have hw : ∀ j, j ≠ r → work j = restore work r v j := by
    intro j hj
    simp only [restore, Function.update_of_ne hj]
  have hc' := MonomialRestore.cursor_replace r (restore work r v) work hw hpark hc
  have hr' := CurrentRestore.ready_replace m L count current.val n R T r sep hraw (restore work r v) work hw hpark
    (fun hR => ⟨hR, hf.fuel⟩) hr
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdr⟩ := hstep inp work out ⟨hc', hr'⟩
  have hdT : T d.work := hdr.2.2.2.2.2.2
  have hwd : ∀ j, j ≠ r → restore d.work r v j = d.work j := by
    intro j hj
    simp only [restore, Function.update_of_ne hj]
  have hpd : Parked (restore d.work r v r) := by
    simp only [restore, Function.update_self]
    exact (reg_regT v).parked
  refine ⟨d, t, ht, hreach, hhalt, hdT.2, hdc.input_read,
    (fun j _ => (hdc.works j).1), hdc.output_read, ?_⟩
  exact ⟨MonomialRestore.cursor_replace r d.work (restore d.work r v) hwd hpd hdc,
    CurrentRestore.ready_replace m L (count + ExactGateCount.reactionCost q) (current.val + 1) n T R
      r sep hraw d.work (restore d.work r v) hwd hpd (fun hT => hT.1) hdr⟩

end JointThermoComplexity.Complexity.CurrentFrame

#print axioms JointThermoComplexity.Complexity.CurrentFrame.hoareTime
