module
public import proofs.JointThermoComplexity.Complexity.ReactionFrame
public import proofs.JointThermoComplexity.Complexity.ReactionTraversal

set_option autoImplicit false
@[expose] public section

/-! The actual outer fuel loop appends exactly the circuit equations of all input reaction records. -/

namespace JointThermoComplexity.Complexity.ReactionLoop
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ReactionPorts NetworkEmitReady ReactionFuel ReactionTraversal
open CircuitSerialization PowerAddressCircuit InvariantLoop

variable {n : ℕ}

def machine (m : ℕ) (r : Fin (m + 15)) : TM (m + 15) := forRegTM (ReactionBuild.machine m) r

def timeBound (L count : ℕ) : ℕ := count * (ReactionBuild.timeBound L + 2) + (count + 2)

theorem stream_congr (offset arity : ℕ) (s t : NetworkCircuit.State n) (he : s = t)
    (inputs : Fin n → Fin arity) (hs : offset + s.size ≤ arity) (ht : offset + t.size ≤ arity) :
    equationStream s.circuit inputs (index offset _ arity hs) =
      equationStream t.circuit inputs (index offset _ arity ht) := by
  cases he
  rfl

def Invariant (m L offset arity : ℕ) (s : NetworkCircuit.State n) (items : List (ReactionCircuit.Reaction n))
    (inputs : Fin n → Fin arity) (h : offset + (s.run items).size ≤ arity)
    (before tail initial : List Bool) (R : (Fin (m + 15) → Tape) → Prop) (i : ℕ) : _root_.Complexity.TapePred (m + 15) :=
  fun inp work out => Cursor (before ++ code (items.take i)) (code (items.drop i) ++ tail)
    (initial ++ equationStream (prefixState s items i).circuit inputs
      (index offset _ arity (by have hs := prefix_le s items i; omega))) inp work out ∧
    Ready m L offset (prefixState s items i).size n R work

theorem framed (m L offset arity : ℕ) (ha : arity ≤ 4 * L) (r : Fin (m + 15)) (sep : Separate m r)
    (s : NetworkCircuit.State n) (items : List (ReactionCircuit.Reaction n)) (inputs : Fin n → Fin arity)
    (hinputs : ∀ i, (inputs i).val = i.val) (h : offset + (s.run items).size ≤ arity) (hcount : n ≤ L)
    (hreactant : ∀ q ∈ items, ∀ i, (q.reactant i).bits.length ≤ L)
    (hproduct : ∀ q ∈ items, ∀ i, (q.product i).bits.length ≤ L)
    (hnum : ∀ q ∈ items, (BitCodec.naturalCode q.numerator).length ≤ L)
    (hden : ∀ q ∈ items, (BitCodec.naturalCode q.denominator).length ≤ L)
    (before tail initial : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → j ≠ accumulator (m + 2) →
      j ≠ power (m + 2) → j ≠ PowerBitState.flag (m + 2) → j ≠ previous (m + 1) →
      j ≠ species (m + 1) → j ≠ saved m → work' j = work j) → R work → R work') :
    (machine m r).HoareTime
      (Frame r items.length 1 (Invariant m L offset arity s items inputs h before tail initial R 0))
      (Frame r items.length 1 (Invariant m L offset arity s items inputs h before tail initial R items.length))
      (timeBound L items.length) := by
  have hb : ∀ i, offset + (prefixState s items i).size ≤ arity := by
    intro i
    have hs := prefix_le s items i
    omega
  have hbody : ∀ i, i < items.length → (ReactionBuild.machine m).HoareTime
      (Frame r items.length (i + 2) (Invariant m L offset arity s items inputs h before tail initial R i))
      (Frame r items.length (i + 2) (Invariant m L offset arity s items inputs h before tail initial R (i + 1)))
      (ReactionBuild.timeBound L) := by
    intro i hi
    have hs : offset + ((prefixState s items i).advance items[i]).size ≤ arity := by
      rw [← prefix_succ s items i hi]
      exact hb (i + 1)
    have hmem := List.getElem_mem hi
    have hf := ReactionFrame.hoareTime m L offset arity items.length (i + 2) ha (by omega)
      r sep (prefixState s items i) items[i] inputs hinputs hs hcount
      (hreactant items[i] hmem) (hproduct items[i] hmem) (hnum items[i] hmem) (hden items[i] hmem)
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
  exact InvariantLoop.hoareTime (ReactionBuild.machine m) r
    (Invariant m L offset arity s items inputs h before tail initial R) (ReactionBuild.timeBound L) items.length hbody

end JointThermoComplexity.Complexity.ReactionLoop

#print axioms JointThermoComplexity.Complexity.ReactionLoop.framed
