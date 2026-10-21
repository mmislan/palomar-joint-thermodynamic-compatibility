module
public import proofs.JointThermoComplexity.Complexity.BoxLoop
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! Canonical entry/exit and an input-length cubic bound for the complete box-record loop. -/

namespace JointThermoComplexity.Complexity.BoxLoopEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxState InvariantLoop NetworkData BoxRecordTraversal CurrentTraversal

def timeBound (L : ℕ) : ℕ := 128 * L ^ 3 + 268 * L ^ 2 + 274 * L + 2

theorem runtime_bound (L n : ℕ) (hn : n ≤ L) : BoxLoop.timeBound L n ≤ timeBound L := by
  unfold BoxLoop.timeBound
  calc
    n * (BoxStep.timeBound L + 2) + (n + 2) ≤ L * (BoxStep.timeBound L + 2) + (L + 2) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hn) (Nat.add_le_add_right hn 2)
    _ = _ := by unfold BoxStep.timeBound timeBound; ring1

theorem hoareTime {n arity : ℕ} (m L : ℕ) (ha : arity ≤ 4 * L) (hn : n ≤ L)
    (r : Fin (m + 15)) (sep : Separate m r) (indices : Fin n → Fin arity) (hindices : ∀ i, (indices i).val = i.val)
    (items : List (Option ClosedBox)) (hlen : items.length = n)
    (hsize : ∀ box ∈ items, BoxOptionalRuntime.Bounded L box)
    (clauses : List (List Bool)) (hcLen : clauses.length = n)
    (hword : ∀ i : Fin n, clauses[i.val]'(by have hi := i.isLt; omega) =
      BoxStep.word (items[i.val]'(by have hi := i.isLt; omega)) (indices i))
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (BoxLoop.machine m r).HoareTime
      (fun inp work out => Cursor before (code items ++ tail) emitted inp work out ∧ Ready m L 0 R work ∧ IsReg n (work r))
      (fun inp work out => Cursor (before ++ code items) tail (emitted ++ output clauses) inp work out ∧
        Ready m L n R work ∧ IsReg n (work r)) (timeBound L) := by
  have hf := BoxLoop.framed m L ha r sep indices hindices items hlen hsize clauses hcLen hword before tail emitted R hR
  exact hf.consequence (by
    rintro inp work out ⟨hc, hr, hv⟩
    refine ⟨hv.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work r n hv.eq_regT]
    simpa only [BoxLoop.Invariant, List.take_zero, List.drop_zero, code, output, List.flatMap_nil,
      List.append_nil] using And.intro hc hr) (by
      intro inp work out hp
      have hitems : items.take n = items := by rw [← hlen, List.take_length]
      have hdrop : items.drop n = [] := by rw [← hlen, List.drop_length]
      have hclauses : clauses.take n = clauses := by rw [← hcLen, List.take_length]
      exact ⟨by simpa only [BoxLoop.Invariant, hitems, hdrop, hclauses, code, List.flatMap_nil, List.nil_append] using hp.on_work.1,
        hp.on_work.2, hp.register⟩) (runtime_bound L n hn)

end JointThermoComplexity.Complexity.BoxLoopEntry

#print axioms JointThermoComplexity.Complexity.BoxLoopEntry.hoareTime
