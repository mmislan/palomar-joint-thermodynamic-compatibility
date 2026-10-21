module
public import proofs.JointThermoComplexity.Complexity.CurrentFrame
public import proofs.JointThermoComplexity.Complexity.CurrentTraversal

set_option autoImplicit false
@[expose] public section

/-! The actual reaction-count loop consumes each record and appends its exact current-equation clause. -/

namespace JointThermoComplexity.Complexity.CurrentLoop
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts CurrentReady CurrentTraversal InvariantLoop

variable {n arity : ℕ}

def machine (m : ℕ) (r : Fin (m + 15)) : TM (m + 15) := forRegTM (CurrentStep.machine m) r

def timeBound (L count : ℕ) : ℕ := count * (CurrentStep.timeBound L + 2) + (count + 2)

def Invariant (m L count first : ℕ) (items : List (ReactionCircuit.Reaction n)) (clauses : List (List Bool))
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop) (i : ℕ) : _root_.Complexity.TapePred (m + 15) :=
  fun inp work out => Cursor (before ++ ReactionTraversal.code (items.take i)) (ReactionTraversal.code (items.drop i) ++ tail)
    (emitted ++ output (clauses.take i)) inp work out ∧ Ready m L (accum count items i) (first + i) n R work

theorem framed (m L count first : ℕ) (ha : arity ≤ 4 * L) (hn : n ≤ L)
    (r : Fin (m + 15)) (sep : ReactionFuel.Separate m r) (hraw : r ≠ raw m)
    (items : List (ReactionCircuit.Reaction n)) (clauses : List (List Bool)) (hc : clauses.length = items.length)
    (current result : Fin items.length → Fin arity)
    (hcurrent : ∀ i, (current i).val = first + i.val)
    (hresult : ∀ i, (result i).val + 1 = accum count items i.val + ExactGateCount.reactionCost items[i.val])
    (hword : ∀ i : Fin items.length, clauses[i.val]'(by have hi := i.isLt; omega) = CurrentRecord.word items[i.val] (current i) (result i))
    (hlen : ∀ q ∈ items, ((DataCodec.reaction n).code q).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ raw m → j ≠ previous (m + 1) → j ≠ species (m + 1) →
      work' j = work j) → R work → R work') :
    (machine m r).HoareTime
      (Frame r items.length 1 (Invariant m L count first items clauses before tail emitted R 0))
      (Frame r items.length 1 (Invariant m L count first items clauses before tail emitted R items.length))
      (timeBound L items.length) := by
  have hbody : ∀ i, i < items.length → (CurrentStep.machine m).HoareTime
      (Frame r items.length (i + 2) (Invariant m L count first items clauses before tail emitted R i))
      (Frame r items.length (i + 2) (Invariant m L count first items clauses before tail emitted R (i + 1)))
      (CurrentStep.timeBound L) := by
    intro i hi
    let j : Fin items.length := ⟨i, hi⟩
    have hf := CurrentFrame.hoareTime m L (accum count items i) items.length (i + 2) (by omega) r sep hraw
      items[i] (current j) (result j) ha hn (hlen items[i] (List.getElem_mem hi)) (hresult j)
      (before ++ ReactionTraversal.code (items.take i)) (ReactionTraversal.code (items.drop (i + 1)) ++ tail)
      (emitted ++ output (clauses.take i)) R hR
    exact hf.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, ReactionTraversal.code_drop_succ items i hi, hcurrent j, j, List.append_assoc] using hp.invariant) (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      have hci : i < clauses.length := by omega
      have he := hword j
      refine ⟨?_, ?_⟩
      · rw [ReactionTraversal.code_take_succ items i hi, output_take_succ clauses i hci, he]
        simpa only [List.append_assoc] using hp.invariant.1
      · simpa only [Invariant, accum_succ count items i hi, hcurrent j, j, Nat.add_assoc] using hp.invariant.2) le_rfl
  exact InvariantLoop.hoareTime (CurrentStep.machine m) r
    (Invariant m L count first items clauses before tail emitted R) (CurrentStep.timeBound L) items.length hbody

end JointThermoComplexity.Complexity.CurrentLoop

#print axioms JointThermoComplexity.Complexity.CurrentLoop.framed
