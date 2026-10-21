module
public import proofs.JointThermoComplexity.Complexity.NetworkEmitReady
public import proofs.JointThermoComplexity.Complexity.NetworkCircuit

set_option autoImplicit false
@[expose] public section

/-! One actual record routine advances the network circuit invariant, retaining the inner species count. -/

namespace JointThermoComplexity.Complexity.ReactionStep
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady MonomialFuel ReactionPorts
open RealCircuit CircuitSerialization PowerAddressCircuit ReactionMonomials

theorem hoareTime {n : ℕ} (m L offset arity : ℕ) (ha : arity ≤ 4 * L)
    (s : NetworkCircuit.State n) (q : ReactionCircuit.Reaction n) (inputs : Fin n → Fin arity)
    (hinputs : ∀ i, (inputs i).val = i.val) (h : offset + (s.advance q).size ≤ arity)
    (hcount : n ≤ L) (hreactant : ∀ i, (q.reactant i).bits.length ≤ L) (hproduct : ∀ i, (q.product i).bits.length ≤ L)
    (hnum : (BitCodec.naturalCode q.numerator).length ≤ L) (hden : (BitCodec.naturalCode q.denominator).length ≤ L)
    (before tail initial : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → j ≠ saved m → work' j = work j) → R work → R work') :
    (ReactionBuild.machine m).HoareTime
      (fun inp work out => Cursor before ((DataCodec.reaction n).code q ++ tail)
        (initial ++ equationStream s.circuit inputs (index offset _ arity
          (by have hs := ReactionCircuit.build_size_ge s.circuit q; change offset + (ReactionCircuit.build s.circuit q).size ≤ arity at h; omega))) inp work out ∧
        NetworkEmitReady.Ready m L offset s.size n R work)
      (fun inp work out => Cursor (before ++ (DataCodec.reaction n).code q) tail
        (initial ++ equationStream (s.advance q).circuit inputs (index offset _ arity h)) inp work out ∧
        NetworkEmitReady.Ready m L offset (s.advance q).size n R work)
      (ReactionBuild.timeBound L) := by
  intro inp work out hp
  rcases hp with ⟨hc, hs, hz, hn, ht, ⟨old, hold, ho⟩, ⟨keep, hkeep, hk⟩, ⟨idx, hidx, hi⟩, hf, hr⟩
  have hb := ReactionBuild.hoareTime m L offset arity old idx keep ha hold hidx hkeep s.circuit q inputs
    hinputs h hcount hreactant hproduct hnum hden before tail initial R hR
  obtain ⟨d, t, htime, hreach, hhalt, hdc, ⟨hds, hdi, hdz, hdn, hdp, hdt, hdr⟩, hdf, hdk⟩ :=
    hb inp work out ⟨hc, hs, hz, hn, ho, ht, hi, hf, hk, hr⟩
  have hprev := (ReactionCircuit.build s.circuit q).output.isLt
  have hsize := ReactionBuildCode.size s.circuit q
  change offset + (ReactionCircuit.build s.circuit q).size ≤ arity at h
  have hpbound : offset + (ReactionCircuit.build s.circuit q).output.val ≤ 4 * L := by omega
  have hkbound : offset + (right s.circuit q.reactant q.product).size + 2 ≤ 4 * L := by omega
  exact ⟨d, t, htime, hreach, hhalt, hdc, hds, hdz, hdn, hdt,
    ⟨_, hpbound, hdp⟩, ⟨_, hkbound, hdk⟩, ⟨n, hcount, hdi⟩, hdf, hdr⟩

end JointThermoComplexity.Complexity.ReactionStep

#print axioms JointThermoComplexity.Complexity.ReactionStep.hoareTime
