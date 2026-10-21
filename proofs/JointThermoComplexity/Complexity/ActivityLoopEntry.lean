module
public import proofs.JointThermoComplexity.Complexity.ActivityLoop

set_option autoImplicit false
@[expose] public section

/-! Canonical entry and exit for the complete species-count positivity loop, including zero species. -/

namespace JointThermoComplexity.Complexity.ActivityLoopEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ActivityState CurrentTraversal InvariantLoop

def timeBound (L : ℕ) : ℕ := 32 * L ^ 3 + 56 * L ^ 2 + 43 * L + 2

theorem runtime_bound (L count : ℕ) (h : count ≤ L) : ActivityLoop.timeBound L count ≤ timeBound L := by
  unfold ActivityLoop.timeBound
  calc
    count * (ActivityStep.timeBound L + 2) + (count + 2) ≤ L * (ActivityStep.timeBound L + 2) + (L + 2) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ h) (Nat.add_le_add_right h 2)
    _ = _ := by unfold ActivityStep.timeBound timeBound; ring1

theorem hoareTime {n arity : ℕ} (m L : ℕ) (ha : arity ≤ 4 * L) (hn : n ≤ L) (r : Fin (m + 15))
    (hsource : r ≠ species (m + 1)) (hzero : r ≠ scratch (m + 2))
    (indices : Fin n → Fin arity) (hindices : ∀ i, (indices i).val = i.val)
    (clauses : List (List Bool)) (hlen : clauses.length = n)
    (hword : ∀ i : Fin n, clauses[i.val]'(by have hi := i.isLt; omega) = ActivityStep.word (indices i))
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → R work → R work') :
    (ActivityLoop.machine m r).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready m 0 R work ∧ IsReg n (work r))
      (fun inp work out => Cursor before input (emitted ++ output clauses) inp work out ∧ Ready m n R work ∧ IsReg n (work r))
      (timeBound L) := by
  have hf := ActivityLoop.framed m L ha r hsource hzero indices hindices clauses hlen hword before input emitted R hR
  exact hf.consequence (by
    rintro inp work out ⟨hc, hr, hv⟩
    refine ⟨hv.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work r n hv.eq_regT]
    simpa only [ActivityLoop.Invariant, List.take_zero, output, List.flatMap_nil, List.append_nil] using And.intro hc hr) (by
      intro inp work out hp
      have hout : clauses.take n = clauses := by rw [← hlen, List.take_length]
      exact ⟨by simpa only [ActivityLoop.Invariant, hout] using hp.on_work.1, hp.on_work.2, hp.register⟩) (runtime_bound L n hn)

end JointThermoComplexity.Complexity.ActivityLoopEntry

#print axioms JointThermoComplexity.Complexity.ActivityLoopEntry.hoareTime
