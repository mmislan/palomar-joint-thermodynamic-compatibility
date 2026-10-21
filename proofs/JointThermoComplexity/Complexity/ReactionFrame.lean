module
public import proofs.JointThermoComplexity.Complexity.ReactionStep
public import proofs.JointThermoComplexity.Complexity.ReactionRestore

set_option autoImplicit false
@[expose] public section

/-! The inner species loops run while the outer reaction fuel keeps its actual positive head. -/

namespace JointThermoComplexity.Complexity.ReactionFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts NetworkEmitReady ReactionFuel
open CircuitSerialization PowerAddressCircuit InvariantLoop

theorem hoareTime {n : ℕ} (m L offset arity v head : ℕ) (ha : arity ≤ 4 * L)
    (hh : 1 ≤ head) (r : Fin (m + 15)) (sep : Separate m r)
    (s : NetworkCircuit.State n) (q : ReactionCircuit.Reaction n) (inputs : Fin n → Fin arity)
    (hinputs : ∀ i, (inputs i).val = i.val) (h : offset + (s.advance q).size ≤ arity)
    (hcount : n ≤ L) (hreactant : ∀ i, (q.reactant i).bits.length ≤ L) (hproduct : ∀ i, (q.product i).bits.length ≤ L)
    (hnum : (BitCodec.naturalCode q.numerator).length ≤ L) (hden : (BitCodec.naturalCode q.denominator).length ≤ L)
    (before tail initial : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → j ≠ saved m → work' j = work j) → R work → R work') :
    (ReactionBuild.machine m).HoareTime
      (Frame r v head (fun inp work out => Cursor before ((DataCodec.reaction n).code q ++ tail)
        (initial ++ equationStream s.circuit inputs (index offset _ arity
          (by have hs := ReactionCircuit.build_size_ge s.circuit q; change offset + (ReactionCircuit.build s.circuit q).size ≤ arity at h; omega))) inp work out ∧
        Ready m L offset s.size n R work))
      (Frame r v head (fun inp work out => Cursor (before ++ (DataCodec.reaction n).code q) tail
        (initial ++ equationStream (s.advance q).circuit inputs (index offset _ arity h)) inp work out ∧
        Ready m L offset (s.advance q).size n R work)) (ReactionBuild.timeBound L) := by
  let T : (Fin (m + 15) → Tape) → Prop := fun work => R (restore work r v) ∧ work r = ⟨head, regCells v⟩
  have hT : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → j ≠ saved m → work' j = work j) → T work → T work' := by
    rintro work work' hw ⟨hr, hf⟩
    refine ⟨hR _ _ ?_ hr, ?_⟩
    · intro j hn ha hp hflag hprev hspecies hsaved
      by_cases hj : j = r
      · subst j; simp only [restore, Function.update_self]
      · simp only [restore, Function.update_of_ne hj]
        exact hw j hn ha hp hflag hprev hspecies hsaved
    · rw [hw r sep.next sep.accumulator sep.power sep.flag sep.previous sep.species sep.saved]
      exact hf
  have hstep := ReactionStep.hoareTime m L offset arity ha s q inputs hinputs h hcount
    hreactant hproduct hnum hden before tail initial T hT
  intro inp work out hf
  obtain ⟨hc, hr⟩ := hf.invariant
  have hpark := MonomialRestore.current_fuel_parked r v head work hh hf.fuel
  have hw : ∀ j, j ≠ r → work j = restore work r v j := by
    intro j hj
    simp only [restore, Function.update_of_ne hj]
  have hc' := MonomialRestore.cursor_replace r (restore work r v) work hw hpark hc
  have hr' := ReactionRestore.ready_replace m L offset s.size n R T r sep (restore work r v) work hw hpark
    (fun hR => ⟨hR, hf.fuel⟩) hr
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdr⟩ := hstep inp work out ⟨hc', hr'⟩
  have hdT : T d.work := hdr.2.2.2.2.2.2.2.2
  have hwd : ∀ j, j ≠ r → restore d.work r v j = d.work j := by
    intro j hj
    simp only [restore, Function.update_of_ne hj]
  have hpd : Parked (restore d.work r v r) := by
    simp only [restore, Function.update_self]
    exact (reg_regT v).parked
  refine ⟨d, t, ht, hreach, hhalt, hdT.2, hdc.input_read,
    (fun j _ => (hdc.works j).1), hdc.output_read, ?_⟩
  exact ⟨MonomialRestore.cursor_replace r d.work (restore d.work r v) hwd hpd hdc,
    ReactionRestore.ready_replace m L offset (s.advance q).size n T R r sep d.work (restore d.work r v)
      hwd hpd (fun hT => hT.1) hdr⟩

end JointThermoComplexity.Complexity.ReactionFrame

#print axioms JointThermoComplexity.Complexity.ReactionFrame.hoareTime
