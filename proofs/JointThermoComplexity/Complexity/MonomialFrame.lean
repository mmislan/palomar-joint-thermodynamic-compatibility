module
public import proofs.JointThermoComplexity.Complexity.MonomialStep
public import proofs.JointThermoComplexity.Complexity.MonomialRestore

set_option autoImplicit false
@[expose] public section

/-! Execute a monomial step at the actual loop-fuel head while its logical invariant sees cell one. -/

namespace JointThermoComplexity.Complexity.MonomialFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady MonomialFuel MonomialRestore
open CircuitSerialization PowerAddressCircuit InvariantLoop

theorem hoareTime {n : ℕ} (m L offset arity idx v head : ℕ) (ha : arity ≤ 4 * L)
    (hi : idx ≤ L) (hh : 1 ≤ head) (r : Fin (m + 14)) (sep : Separate m r)
    (s : MonomialCircuit.State n) (item : Fin n × ℕ) (inputs : Fin n → Fin arity)
    (h : offset + (s.advance item).size ≤ arity) (hlen : item.2.bits.length ≤ L) (hidx : (inputs item.1).val = idx)
    (before tail initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ accumulator (m + 1) →
      j ≠ power (m + 1) → j ≠ PowerBitState.flag (m + 1) → j ≠ previous m → j ≠ species m →
      work' j = work j) → R work → R work') :
    (MonomialStep.machine m).HoareTime
      (Frame r v head (fun inp work out => Cursor before (BitCodec.naturalCode item.2 ++ tail)
        (initial ++ equationStream s.circuit inputs (index offset _ arity (by have hs := s.advance_size_ge item; omega))) inp work out ∧
        Ready m L offset s idx R work))
      (Frame r v head (fun inp work out => Cursor (before ++ BitCodec.naturalCode item.2) tail
        (initial ++ equationStream (s.advance item).circuit inputs (index offset _ arity h)) inp work out ∧
        Ready m L offset (s.advance item) (idx + 1) R work)) (MonomialStep.timeBound L) := by
  let T : (Fin (m + 14) → Tape) → Prop := fun work => R (restore work r v) ∧ work r = ⟨head, regCells v⟩
  have hT : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ accumulator (m + 1) →
      j ≠ power (m + 1) → j ≠ PowerBitState.flag (m + 1) → j ≠ previous m → j ≠ species m →
      work' j = work j) → T work → T work' := by
    rintro work work' hw ⟨hr, hf⟩
    refine ⟨hR _ _ ?_ hr, ?_⟩
    · intro j hn ha hp hflag hprev hspecies
      by_cases hj : j = r
      · subst j; simp only [restore, Function.update_self]
      · simp only [restore, Function.update_of_ne hj]
        exact hw j hn ha hp hflag hprev hspecies
    · rw [hw r sep.next sep.accumulator sep.power sep.flag sep.previous sep.species]
      exact hf
  have hstep := MonomialStep.hoareTime m L offset arity idx ha hi s item inputs h hlen hidx before tail initial T hT
  intro inp work out hf
  obtain ⟨hc, hr⟩ := hf.invariant
  have hpark := current_fuel_parked r v head work hh hf.fuel
  have hw : ∀ j, j ≠ r → work j = restore work r v j := by
    intro j hj
    simp only [restore, Function.update_of_ne hj]
  have hc' := cursor_replace r (restore work r v) work hw hpark hc
  have hr' := ready_replace L offset idx s R T r sep (restore work r v) work hw hpark
    (fun hR => ⟨hR, hf.fuel⟩) hr
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdr⟩ := hstep inp work out ⟨hc', hr'⟩
  have hdT : T d.work := by
    rcases hdr with ⟨_, _, _, _, _, _, hT⟩
    exact hT
  have hwd : ∀ j, j ≠ r → restore d.work r v j = d.work j := by
    intro j hj
    simp only [restore, Function.update_of_ne hj]
  have hpd : Parked (restore d.work r v r) := by
    simp only [restore, Function.update_self]
    exact (reg_regT v).parked
  refine ⟨d, t, ht, hreach, hhalt, hdT.2, hdc.input_read,
    (fun j _ => (hdc.works j).1), hdc.output_read, ?_⟩
  exact ⟨cursor_replace r d.work (restore d.work r v) hwd hpd hdc,
    ready_replace L offset (idx + 1) (s.advance item) T R r sep d.work (restore d.work r v)
      hwd hpd (fun hT => hT.1) hdr⟩

end JointThermoComplexity.Complexity.MonomialFrame

#print axioms JointThermoComplexity.Complexity.MonomialFrame.hoareTime
