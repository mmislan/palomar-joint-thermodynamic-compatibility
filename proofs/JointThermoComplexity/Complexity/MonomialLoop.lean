module
public import proofs.JointThermoComplexity.Complexity.MonomialFrame
public import proofs.JointThermoComplexity.Complexity.MonomialTraversal

set_option autoImplicit false
@[expose] public section

/-! The actual fuel-controlled loop traverses every canonical exponent field in forward order. -/

namespace JointThermoComplexity.Complexity.MonomialLoop
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady MonomialFuel MonomialTraversal
open CircuitSerialization PowerAddressCircuit InvariantLoop

variable {n : ℕ}

def machine (m : ℕ) (r : Fin (m + 14)) : TM (m + 14) := forRegTM (MonomialStep.machine m) r

def timeBound (L count : ℕ) : ℕ := count * (MonomialStep.timeBound L + 2) + (count + 2)

theorem stream_congr (offset arity : ℕ) (s t : MonomialCircuit.State n) (he : s = t)
    (inputs : Fin n → Fin arity) (hs : offset + s.size ≤ arity) (ht : offset + t.size ≤ arity) :
    equationStream s.circuit inputs (index offset _ arity hs) =
      equationStream t.circuit inputs (index offset _ arity ht) := by
  cases he
  rfl

def Invariant (m L offset arity : ℕ) (s : MonomialCircuit.State n) (items : List (Fin n × ℕ))
    (inputs : Fin n → Fin arity) (h : offset + (s.runTerms items).size ≤ arity)
    (before tail initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop) (i : ℕ) : _root_.Complexity.TapePred (m + 14) :=
  fun inp work out => Cursor (before ++ code (items.take i)) (code (items.drop i) ++ tail)
    (initial ++ equationStream (prefixState s items i).circuit inputs
      (index offset _ arity (by have hs := prefix_le s items i; omega))) inp work out ∧
    Ready m L offset (prefixState s items i) i R work

theorem framed (m L offset arity : ℕ) (ha : arity ≤ 4 * L) (r : Fin (m + 14)) (sep : Separate m r)
    (s : MonomialCircuit.State n) (items : List (Fin n × ℕ)) (inputs : Fin n → Fin arity)
    (h : offset + (s.runTerms items).size ≤ arity) (hcount : items.length ≤ L)
    (hbits : ∀ item ∈ items, item.2.bits.length ≤ L)
    (hidx : ∀ i (hi : i < items.length), (inputs items[i].1).val = i)
    (before tail initial : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ accumulator (m + 1) →
      j ≠ power (m + 1) → j ≠ PowerBitState.flag (m + 1) → j ≠ previous m → j ≠ species m →
      work' j = work j) → R work → R work') :
    (machine m r).HoareTime
      (Frame r items.length 1 (Invariant m L offset arity s items inputs h before tail initial R 0))
      (Frame r items.length 1 (Invariant m L offset arity s items inputs h before tail initial R items.length))
      (timeBound L items.length) := by
  have hb : ∀ i, offset + (prefixState s items i).size ≤ arity := by
    intro i
    have hs := prefix_le s items i
    omega
  have hbody : ∀ i, i < items.length → (MonomialStep.machine m).HoareTime
      (Frame r items.length (i + 2) (Invariant m L offset arity s items inputs h before tail initial R i))
      (Frame r items.length (i + 2) (Invariant m L offset arity s items inputs h before tail initial R (i + 1)))
      (MonomialStep.timeBound L) := by
    intro i hi
    have hs : offset + ((prefixState s items i).advance items[i]).size ≤ arity := by
      rw [← prefix_succ s items i hi]
      exact hb (i + 1)
    have hf := MonomialFrame.hoareTime m L offset arity i items.length (i + 2) ha (by omega) (by omega)
      r sep (prefixState s items i) items[i] inputs hs (hbits items[i] (List.getElem_mem hi)) (hidx i hi)
      (before ++ code (items.take i)) (code (items.drop (i + 1)) ++ tail) initial R hR
    exact hf.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, code_drop_succ items i hi, List.append_assoc] using hp.invariant) (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      have heq := stream_congr offset arity (prefixState s items (i + 1))
        ((prefixState s items i).advance items[i]) (prefix_succ s items i hi) inputs (hb (i + 1)) hs
      refine ⟨?_, ?_⟩
      · change Cursor (before ++ code (items.take (i + 1))) (code (items.drop (i + 1)) ++ tail)
          (initial ++ equationStream (prefixState s items (i + 1)).circuit inputs
            (index offset _ arity (hb (i + 1)))) inp (restore work r items.length) out
        rw [heq, code_take_succ items i hi]
        simpa only [List.append_assoc] using hp.invariant.1
      · simpa only [prefix_succ s items i hi] using hp.invariant.2) le_rfl
  exact InvariantLoop.hoareTime (MonomialStep.machine m) r
    (Invariant m L offset arity s items inputs h before tail initial R) (MonomialStep.timeBound L) items.length hbody

end JointThermoComplexity.Complexity.MonomialLoop

#print axioms JointThermoComplexity.Complexity.MonomialLoop.framed
