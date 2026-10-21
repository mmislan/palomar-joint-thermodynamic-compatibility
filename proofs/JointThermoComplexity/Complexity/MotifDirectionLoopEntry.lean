module
public import proofs.JointThermoComplexity.Complexity.MotifDirectionLoop
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! Canonical count entry/exit and a cubic bound for the complete direction loop, including zero iterations. -/

namespace JointThermoComplexity.Complexity.MotifDirectionLoopEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifDirectionState MotifDirectionFrame InvariantLoop CurrentTraversal

def timeBound (L : ℕ) : ℕ := 32 * L ^ 3 + 56 * L ^ 2 + 52 * L + 2

theorem runtime_bound (L n : ℕ) (hn : n ≤ L) : MotifDirectionLoop.timeBound L n ≤ timeBound L := by
  unfold MotifDirectionLoop.timeBound
  calc n * (MotifDirectionStep.timeBound L + 2) + (n + 2) ≤
       L * (MotifDirectionStep.timeBound L + 2) + (L + 2) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hn) (Nat.add_le_add_right hn 2)
       _ = _ := by unfold MotifDirectionStep.timeBound timeBound; ring1

theorem hoareTime {n arity : ℕ} (m L base : ℕ) (ha : arity ≤ 4 * L) (hn : n ≤ L)
    (r : Fin (m + 15)) (sep : BoxState.Separate m r) (indices : Fin n → Fin arity)
    (hindices : ∀ i, (indices i).val = base + i.val) (mask flags : List Bool)
    (hmLen : mask.length = n) (hfLen : flags.length = n) (clauses : List (List Bool)) (hcLen : clauses.length = n)
    (hword : ∀ j : Fin n, clauses[j.val]'(by have hj := j.isLt; omega) =
      MotifDirectionClause.word (mask[j.val]'(by have hj := j.isLt; omega))
        (flags[j.val]'(by have hj := j.isLt; omega)) (indices j))
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (MotifDirectionLoop.machine m r).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ State m L base mask flags 0 R work ∧ IsReg n (work r))
      (fun inp work out => Cursor before input (emitted ++ output clauses) inp work out ∧
        State m L (base + n) mask flags n R work ∧ IsReg n (work r)) (timeBound L) := by
  have hf := MotifDirectionLoop.framed m L base ha hn r sep indices hindices mask flags hmLen hfLen
    clauses hcLen hword before input emitted R hR
  exact hf.consequence (by
    rintro inp work out ⟨hc, hp, hr⟩
    refine ⟨hr.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work r n hr.eq_regT]
    simpa only [MotifDirectionLoop.Invariant, List.take_zero, output, List.flatMap_nil, List.append_nil, Nat.add_zero]
      using And.intro hc hp) (by
        intro inp work out hp
        have hclauses : clauses.take n = clauses := by rw [← hcLen, List.take_length]
        exact ⟨by simpa only [MotifDirectionLoop.Invariant, hclauses] using hp.on_work.1,
          hp.on_work.2, hp.register⟩) (runtime_bound L n hn)

end JointThermoComplexity.Complexity.MotifDirectionLoopEntry

#print axioms JointThermoComplexity.Complexity.MotifDirectionLoopEntry.hoareTime
