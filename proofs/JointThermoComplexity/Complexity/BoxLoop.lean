module
public import proofs.JointThermoComplexity.Complexity.BoxRecordTraversal

set_option autoImplicit false
@[expose] public section

/-! The actual species-count loop consumes one optional box and emits one indexed clause per iteration. -/

namespace JointThermoComplexity.Complexity.BoxLoop
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxState InvariantLoop NetworkData BoxRecordTraversal CurrentTraversal

def machine (m : ℕ) (r : Fin (m + 15)) : TM (m + 15) := forRegTM (BoxStep.machine m) r

def timeBound (L count : ℕ) : ℕ := count * (BoxStep.timeBound L + 2) + (count + 2)

def Invariant (m L : ℕ) (items : List (Option ClosedBox)) (clauses : List (List Bool))
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop) (i : ℕ) :
    _root_.Complexity.TapePred (m + 15) := fun inp work out =>
  Cursor (before ++ code (items.take i)) (code (items.drop i) ++ tail)
    (emitted ++ output (clauses.take i)) inp work out ∧ Ready m L i R work

theorem framed {n arity : ℕ} (m L : ℕ) (ha : arity ≤ 4 * L) (r : Fin (m + 15)) (sep : Separate m r)
    (indices : Fin n → Fin arity) (hindices : ∀ i, (indices i).val = i.val)
    (items : List (Option ClosedBox)) (hlen : items.length = n)
    (hsize : ∀ box ∈ items, BoxOptionalRuntime.Bounded L box)
    (clauses : List (List Bool)) (hcLen : clauses.length = n)
    (hword : ∀ i : Fin n, clauses[i.val]'(by have hi := i.isLt; omega) =
      BoxStep.word (items[i.val]'(by have hi := i.isLt; omega)) (indices i))
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m r).HoareTime
      (Frame r n 1 (Invariant m L items clauses before tail emitted R 0))
      (Frame r n 1 (Invariant m L items clauses before tail emitted R n)) (timeBound L n) := by
  have hbody : ∀ i, i < n → (BoxStep.machine m).HoareTime
      (Frame r n (i + 2) (Invariant m L items clauses before tail emitted R i))
      (Frame r n (i + 2) (Invariant m L items clauses before tail emitted R (i + 1))) (BoxStep.timeBound L) := by
    intro i hi
    let j : Fin n := ⟨i, hi⟩
    have hitem : i < items.length := by omega
    have hclause : i < clauses.length := by omega
    have hs := BoxFrame.hoareTime m L n (i + 2) (by omega) r sep ha items[i]
      (hsize items[i] (List.getElem_mem hitem)) (indices j)
      (before ++ code (items.take i)) (code (items.drop (i + 1)) ++ tail)
      (emitted ++ output (clauses.take i)) R hR
    exact hs.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, code_drop_succ items i hitem, List.append_assoc, hindices j, j] using hp.invariant) (by
        intro inp work out hp
        refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
        have hw := hword j
        change Cursor (before ++ code (items.take (i + 1))) (code (items.drop (i + 1)) ++ tail)
          (emitted ++ output (clauses.take (i + 1))) inp (restore work r n) out ∧ Ready m L (i + 1) R (restore work r n)
        rw [code_take_succ items i hitem, output_take_succ clauses i hclause, hw]
        simpa only [List.append_assoc, hindices j, j] using hp.invariant) le_rfl
  exact InvariantLoop.hoareTime (BoxStep.machine m) r (Invariant m L items clauses before tail emitted R)
    (BoxStep.timeBound L) n hbody

end JointThermoComplexity.Complexity.BoxLoop

#print axioms JointThermoComplexity.Complexity.BoxLoop.framed
