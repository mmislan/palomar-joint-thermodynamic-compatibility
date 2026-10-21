module
public import proofs.JointThermoComplexity.Complexity.ReactionLoopEntry

set_option autoImplicit false
@[expose] public section

/-! The concrete reaction-count machine consumes the actual finite reaction table and emits its dense circuit. -/

namespace JointThermoComplexity.Complexity.NetworkBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts NetworkEmitReady
open CircuitSerialization PowerAddressCircuit FiniteCodec

def machine (m : ℕ) : TM (m + 15) := ReactionLoop.machine m (ReactionFuel.slot m)

theorem table_code {n r : ℕ} (qs : Fin r → ReactionCircuit.Reaction n) :
    ReactionTraversal.code (List.ofFn qs) = functionCode (DataCodec.reaction n) qs := by
  rw [functionCode_eq_flatMap]
  rfl

theorem hoareTime {n r : ℕ} (m L offset arity : ℕ) (ha : arity ≤ 4 * L)
    (qs : Fin r → ReactionCircuit.Reaction n) (inputs : Fin n → Fin arity)
    (hinputs : ∀ i, (inputs i).val = i.val) (h : offset + (NetworkCircuit.dense qs).size ≤ arity)
    (hcount : n ≤ L) (hlen : r ≤ L)
    (hreactant : ∀ j i, ((qs j).reactant i).bits.length ≤ L)
    (hproduct : ∀ j i, ((qs j).product i).bits.length ≤ L)
    (hnum : ∀ j, (BitCodec.naturalCode (qs j).numerator).length ≤ L)
    (hden : ∀ j, (BitCodec.naturalCode (qs j).denominator).length ≤ L)
    (before tail initial : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → j ≠ saved m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before (functionCode (DataCodec.reaction n) qs ++ tail) initial inp work out ∧
        Ready m L offset 0 n R work ∧ IsReg r (work (ReactionFuel.slot m)))
      (fun inp work out => Cursor (before ++ functionCode (DataCodec.reaction n) qs) tail
        (initial ++ equationStream (NetworkCircuit.dense qs).circuit inputs (index offset _ arity h)) inp work out ∧
        Ready m L offset (NetworkCircuit.dense qs).size n R work ∧ IsReg r (work (ReactionFuel.slot m)))
      (ReactionLoopEntry.timeBound L) := by
  have hreactant' : ∀ q ∈ List.ofFn qs, ∀ i, (q.reactant i).bits.length ≤ L := by
    intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact hreactant j
  have hproduct' : ∀ q ∈ List.ofFn qs, ∀ i, (q.product i).bits.length ≤ L := by
    intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact hproduct j
  have hnum' : ∀ q ∈ List.ofFn qs, (BitCodec.naturalCode q.numerator).length ≤ L := by
    intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact hnum j
  have hden' : ∀ q ∈ List.ofFn qs, (BitCodec.naturalCode q.denominator).length ≤ L := by
    intro q hq
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
    exact hden j
  have ht := ReactionLoopEntry.hoareTime m L offset arity ha (ReactionFuel.slot m) (ReactionFuel.slot_separate m)
    (⟨0, .nil, []⟩ : NetworkCircuit.State n) (List.ofFn qs) inputs hinputs h hcount
    (by simpa only [List.length_ofFn] using hlen) hreactant' hproduct' hnum' hden' before tail initial R hR
  exact ht.consequence
    (fun _ _ _ hp => by simpa only [table_code, CircuitSerialization.equationStream, List.append_nil, List.length_ofFn] using hp)
    (fun _ _ _ hp => by simpa only [table_code, List.length_ofFn, NetworkCircuit.dense, NetworkCircuit.build] using hp) le_rfl

end JointThermoComplexity.Complexity.NetworkBuild

#print axioms JointThermoComplexity.Complexity.NetworkBuild.hoareTime
