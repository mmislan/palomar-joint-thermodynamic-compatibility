module
public import proofs.JointThermoComplexity.Complexity.ReactionLoop

set_option autoImplicit false
@[expose] public section

/-! Enter and leave the reaction loop with canonical outer fuel and an exact full equation stream. -/

namespace JointThermoComplexity.Complexity.ReactionLoopEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts NetworkEmitReady ReactionFuel ReactionTraversal
open CircuitSerialization PowerAddressCircuit InvariantLoop

def timeBound (L : ℕ) : ℕ := 384 * L ^ 5 + 1104 * L ^ 4 + 1512 * L ^ 3 + 1228 * L ^ 2 + 450 * L + 2

theorem runtime_bound (L count : ℕ) (h : count ≤ L) : ReactionLoop.timeBound L count ≤ timeBound L := by
  unfold ReactionLoop.timeBound
  calc
    count * (ReactionBuild.timeBound L + 2) + (count + 2) ≤ L * (ReactionBuild.timeBound L + 2) + (L + 2) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ h) (Nat.add_le_add_right h 2)
    _ = _ := by unfold ReactionBuild.timeBound timeBound; ring1

theorem hoareTime {n : ℕ} (m L offset arity : ℕ) (ha : arity ≤ 4 * L)
    (r : Fin (m + 15)) (sep : Separate m r) (s : NetworkCircuit.State n)
    (items : List (ReactionCircuit.Reaction n)) (inputs : Fin n → Fin arity)
    (hinputs : ∀ i, (inputs i).val = i.val) (h : offset + (s.run items).size ≤ arity)
    (hcount : n ≤ L) (hlen : items.length ≤ L)
    (hreactant : ∀ q ∈ items, ∀ i, (q.reactant i).bits.length ≤ L)
    (hproduct : ∀ q ∈ items, ∀ i, (q.product i).bits.length ≤ L)
    (hnum : ∀ q ∈ items, (BitCodec.naturalCode q.numerator).length ≤ L)
    (hden : ∀ q ∈ items, (BitCodec.naturalCode q.denominator).length ≤ L)
    (before tail initial : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → j ≠ saved m → work' j = work j) → R work → R work') :
    (ReactionLoop.machine m r).HoareTime
      (fun inp work out => Cursor before (code items ++ tail)
        (initial ++ equationStream s.circuit inputs (index offset _ arity (by have hs := run_size_ge s items; omega))) inp work out ∧
        Ready m L offset s.size n R work ∧ IsReg items.length (work r))
      (fun inp work out => Cursor (before ++ code items) tail
        (initial ++ equationStream (s.run items).circuit inputs (index offset _ arity h)) inp work out ∧
        Ready m L offset (s.run items).size n R work ∧ IsReg items.length (work r))
      (timeBound L) := by
  have hf := ReactionLoop.framed m L offset arity ha r sep s items inputs hinputs h hcount
    hreactant hproduct hnum hden before tail initial R hR
  exact hf.consequence (by
    rintro inp work out ⟨hc, hr, hv⟩
    refine ⟨hv.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work r items.length hv.eq_regT]
    simpa only [ReactionLoop.Invariant, prefix_zero, List.take_zero, code, List.flatMap_nil,
      List.append_nil, List.drop_zero] using (And.intro hc hr)) (by
    intro inp work out hp
    have hs : offset + (prefixState s items items.length).size ≤ arity := by
      rw [prefix_length]
      exact h
    have heq := ReactionLoop.stream_congr offset arity (prefixState s items items.length) (s.run items)
      (prefix_length s items) inputs hs h
    refine ⟨?_, ?_, hp.register⟩
    · rw [← heq]
      simpa only [ReactionLoop.Invariant, List.take_length, List.drop_length, code,
        List.flatMap_nil, List.nil_append] using hp.on_work.1
    · simpa only [ReactionLoop.Invariant, prefix_length] using hp.on_work.2) (runtime_bound L items.length hlen)

end JointThermoComplexity.Complexity.ReactionLoopEntry

#print axioms JointThermoComplexity.Complexity.ReactionLoopEntry.hoareTime
