module
public import proofs.JointThermoComplexity.Complexity.MonomialLoop

set_option autoImplicit false
@[expose] public section

/-! Enter the loop from actual canonical fuel and return the exact full equation stream with fuel restored. -/

namespace JointThermoComplexity.Complexity.MonomialLoopEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady MonomialFuel MonomialTraversal
open CircuitSerialization PowerAddressCircuit InvariantLoop

theorem runtime_bound (L count : ℕ) (h : count ≤ L) :
    MonomialLoop.timeBound L count ≤ 192 * L ^ 4 + 552 * L ^ 3 + 580 * L ^ 2 + 225 * L + 2 := by
  unfold MonomialLoop.timeBound
  calc
    count * (MonomialStep.timeBound L + 2) + (count + 2) ≤ L * (MonomialStep.timeBound L + 2) + (L + 2) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ h) (Nat.add_le_add_right h 2)
    _ = _ := by unfold MonomialStep.timeBound; ring1

theorem hoareTime {n : ℕ} (m L offset arity : ℕ) (ha : arity ≤ 4 * L)
    (r : Fin (m + 14)) (sep : Separate m r) (s : MonomialCircuit.State n)
    (items : List (Fin n × ℕ)) (inputs : Fin n → Fin arity)
    (h : offset + (s.runTerms items).size ≤ arity) (hcount : items.length ≤ L)
    (hbits : ∀ item ∈ items, item.2.bits.length ≤ L)
    (hidx : ∀ i (hi : i < items.length), (inputs items[i].1).val = i)
    (before tail initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ accumulator (m + 1) →
      j ≠ power (m + 1) → j ≠ PowerBitState.flag (m + 1) → j ≠ previous m → j ≠ species m →
      work' j = work j) → R work → R work') :
    (MonomialLoop.machine m r).HoareTime
      (fun inp work out => Cursor before (code items ++ tail)
        (initial ++ equationStream s.circuit inputs (index offset _ arity (by have hs := s.runTerms_size_ge items; omega))) inp work out ∧
        Ready m L offset s 0 R work ∧ IsReg items.length (work r))
      (fun inp work out => Cursor (before ++ code items) tail
        (initial ++ equationStream (s.runTerms items).circuit inputs (index offset _ arity h)) inp work out ∧
        Ready m L offset (s.runTerms items) items.length R work ∧ IsReg items.length (work r))
      (192 * L ^ 4 + 552 * L ^ 3 + 580 * L ^ 2 + 225 * L + 2) := by
  have hf := MonomialLoop.framed m L offset arity ha r sep s items inputs h hcount hbits hidx before tail initial R hR
  exact hf.consequence (by
    rintro inp work out ⟨hc, hr, hv⟩
    refine ⟨hv.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work r items.length hv.eq_regT]
    simpa only [MonomialLoop.Invariant, prefix_zero, List.take_zero, code, List.flatMap_nil,
      List.append_nil, List.drop_zero] using (And.intro hc hr)) (by
    intro inp work out hp
    have hs : offset + (prefixState s items items.length).size ≤ arity := by
      rw [prefix_length]
      exact h
    have heq := MonomialLoop.stream_congr offset arity (prefixState s items items.length) (s.runTerms items)
      (prefix_length s items) inputs hs h
    refine ⟨?_, ?_, hp.register⟩
    · rw [← heq]
      simpa only [MonomialLoop.Invariant, List.take_length, List.drop_length, code,
        List.flatMap_nil, List.nil_append] using hp.on_work.1
    · simpa only [MonomialLoop.Invariant, prefix_length] using hp.on_work.2) (runtime_bound L items.length hcount)

end JointThermoComplexity.Complexity.MonomialLoopEntry

#print axioms JointThermoComplexity.Complexity.MonomialLoopEntry.hoareTime
