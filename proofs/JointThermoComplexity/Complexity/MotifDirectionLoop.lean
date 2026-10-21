module
public import proofs.JointThermoComplexity.Complexity.MotifDirectionFuelFrame
public import proofs.JointThermoComplexity.Complexity.CurrentTraversal

set_option autoImplicit false
@[expose] public section

/-! The retained reaction-count loop emits one direction clause and advances both stored-vector positions per iteration. -/

namespace JointThermoComplexity.Complexity.MotifDirectionLoop
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifDirectionState MotifDirectionFrame InvariantLoop CurrentTraversal

def machine (m : ℕ) (r : Fin (m + 15)) : TM (m + 15) := forRegTM (MotifDirectionStep.machine m) r

def timeBound (L count : ℕ) : ℕ := count * (MotifDirectionStep.timeBound L + 2) + (count + 2)

def Invariant (m L base : ℕ) (mask flags : List Bool) (clauses : List (List Bool))
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop) (i : ℕ) :
    _root_.Complexity.TapePred (m + 15) := fun inp work out =>
  Cursor before input (emitted ++ output (clauses.take i)) inp work out ∧ State m L (base + i) mask flags i R work

theorem framed {n arity : ℕ} (m L base : ℕ) (ha : arity ≤ 4 * L) (hn : n ≤ L)
    (r : Fin (m + 15)) (sep : BoxState.Separate m r) (indices : Fin n → Fin arity)
    (hindices : ∀ i, (indices i).val = base + i.val) (mask flags : List Bool)
    (hmLen : mask.length = n) (hfLen : flags.length = n)
    (clauses : List (List Bool)) (hcLen : clauses.length = n)
    (hword : ∀ j : Fin n, clauses[j.val]'(by have hj := j.isLt; omega) =
      MotifDirectionClause.word (mask[j.val]'(by have hj := j.isLt; omega))
        (flags[j.val]'(by have hj := j.isLt; omega)) (indices j))
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m r).HoareTime
      (Frame r n 1 (Invariant m L base mask flags clauses before input emitted R 0))
      (Frame r n 1 (Invariant m L base mask flags clauses before input emitted R n)) (timeBound L n) := by
  have hbody : ∀ i, i < n → (MotifDirectionStep.machine m).HoareTime
      (Frame r n (i + 2) (Invariant m L base mask flags clauses before input emitted R i))
      (Frame r n (i + 2) (Invariant m L base mask flags clauses before input emitted R (i + 1)))
      (MotifDirectionStep.timeBound L) := by
    intro i hi
    let j : Fin n := ⟨i, hi⟩
    have hclause : i < clauses.length := by omega
    have hs := MotifDirectionFuelFrame.hoareTime m L n (i + 2) (by omega) r sep ha (indices j) mask flags i
      (by omega) (by omega) (by omega) (by omega) before input (emitted ++ output (clauses.take i)) R hR
    exact hs.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, hindices j, j] using hp.invariant) (by
        intro inp work out hp
        refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
        change Cursor before input (emitted ++ output (clauses.take (i + 1))) inp (restore work r n) out ∧
          State m L (base + (i + 1)) mask flags (i + 1) R (restore work r n)
        rw [output_take_succ clauses i hclause, hword j]
        simpa only [List.append_assoc, hindices j, j, Nat.add_assoc] using hp.invariant) le_rfl
  exact InvariantLoop.hoareTime (MotifDirectionStep.machine m) r
    (Invariant m L base mask flags clauses before input emitted R) (MotifDirectionStep.timeBound L) n hbody

end JointThermoComplexity.Complexity.MotifDirectionLoop

#print axioms JointThermoComplexity.Complexity.MotifDirectionLoop.framed
