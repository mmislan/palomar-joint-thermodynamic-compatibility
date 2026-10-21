module
public import proofs.JointThermoComplexity.Complexity.ActivityFrame
public import proofs.JointThermoComplexity.Complexity.CurrentTraversal

set_option autoImplicit false
@[expose] public section

/-! The actual species-count loop emits positivity clauses in ascending activity-index order. -/

namespace JointThermoComplexity.Complexity.ActivityLoop
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ActivityState CurrentTraversal InvariantLoop

def machine (m : ℕ) (r : Fin (m + 15)) : TM (m + 15) := forRegTM (ActivityStep.machine m) r

def timeBound (L count : ℕ) : ℕ := count * (ActivityStep.timeBound L + 2) + (count + 2)

def Invariant (m : ℕ) (clauses : List (List Bool)) (before input emitted : List Bool)
    (R : (Fin (m + 15) → Tape) → Prop) (i : ℕ) : _root_.Complexity.TapePred (m + 15) :=
  fun inp work out => Cursor before input (emitted ++ output (clauses.take i)) inp work out ∧ Ready m i R work

theorem framed {n arity : ℕ} (m L : ℕ) (ha : arity ≤ 4 * L) (r : Fin (m + 15))
    (hsource : r ≠ species (m + 1)) (hzero : r ≠ scratch (m + 2))
    (indices : Fin n → Fin arity) (hindices : ∀ i, (indices i).val = i.val)
    (clauses : List (List Bool)) (hlen : clauses.length = n)
    (hword : ∀ i : Fin n, clauses[i.val]'(by have hi := i.isLt; omega) = ActivityStep.word (indices i))
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → R work → R work') :
    (machine m r).HoareTime
      (Frame r n 1 (Invariant m clauses before input emitted R 0))
      (Frame r n 1 (Invariant m clauses before input emitted R n)) (timeBound L n) := by
  have hbody : ∀ i, i < n → (ActivityStep.machine m).HoareTime
      (Frame r n (i + 2) (Invariant m clauses before input emitted R i))
      (Frame r n (i + 2) (Invariant m clauses before input emitted R (i + 1))) (ActivityStep.timeBound L) := by
    intro i hi
    let j : Fin n := ⟨i, hi⟩
    have hs := ActivityFrame.hoareTime m L n (i + 2) (by omega) r hsource hzero ha (indices j)
      before input (emitted ++ output (clauses.take i)) R hR
    exact hs.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, hindices j, j] using hp.invariant) (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      have hci : i < clauses.length := by omega
      have hw := hword j
      refine ⟨?_, ?_⟩
      · rw [output_take_succ clauses i hci, hw]
        simpa only [List.append_assoc] using hp.invariant.1
      · simpa only [Invariant, hindices j, j] using hp.invariant.2) le_rfl
  exact InvariantLoop.hoareTime (ActivityStep.machine m) r (Invariant m clauses before input emitted R)
    (ActivityStep.timeBound L) n hbody

end JointThermoComplexity.Complexity.ActivityLoop

#print axioms JointThermoComplexity.Complexity.ActivityLoop.framed
