module
public import proofs.JointThermoComplexity.Complexity.CurrentLoop

set_option autoImplicit false
@[expose] public section

/-! Canonical entry and exit for the complete current-record loop, with a cubic input-length bound. -/

namespace JointThermoComplexity.Complexity.CurrentLoopEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts CurrentReady CurrentTraversal InvariantLoop

def timeBound (L : ℕ) : ℕ := 66 * L ^ 3 + 164 * L ^ 2 + 123 * L + 2

theorem runtime_bound (L count : ℕ) (h : count ≤ L) : CurrentLoop.timeBound L count ≤ timeBound L := by
  unfold CurrentLoop.timeBound
  calc
    count * (CurrentStep.timeBound L + 2) + (count + 2) ≤ L * (CurrentStep.timeBound L + 2) + (L + 2) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ h) (Nat.add_le_add_right h 2)
    _ = _ := by unfold CurrentStep.timeBound timeBound; ring1

theorem hoareTime {n arity : ℕ} (m L count first : ℕ) (ha : arity ≤ 4 * L) (hn : n ≤ L)
    (r : Fin (m + 15)) (sep : ReactionFuel.Separate m r) (hraw : r ≠ raw m)
    (items : List (ReactionCircuit.Reaction n)) (clauses : List (List Bool)) (hc : clauses.length = items.length)
    (current result : Fin items.length → Fin arity)
    (hcurrent : ∀ i, (current i).val = first + i.val)
    (hresult : ∀ i, (result i).val + 1 = accum count items i.val + ExactGateCount.reactionCost items[i.val])
    (hword : ∀ i : Fin items.length, clauses[i.val]'(by have hi := i.isLt; omega) = CurrentRecord.word items[i.val] (current i) (result i))
    (hcount : items.length ≤ L) (hlen : ∀ q ∈ items, ((DataCodec.reaction n).code q).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ raw m → j ≠ previous (m + 1) → j ≠ species (m + 1) →
      work' j = work j) → R work → R work') :
    (CurrentLoop.machine m r).HoareTime
      (fun inp work out => Cursor before (ReactionTraversal.code items ++ tail) emitted inp work out ∧
        Ready m L count first n R work ∧ IsReg items.length (work r))
      (fun inp work out => Cursor (before ++ ReactionTraversal.code items) tail (emitted ++ output clauses) inp work out ∧
        Ready m L (count + ExactGateCount.networkCost items) (first + items.length) n R work ∧ IsReg items.length (work r))
      (timeBound L) := by
  have hf := CurrentLoop.framed m L count first ha hn r sep hraw items clauses hc current result
    hcurrent hresult hword hlen before tail emitted R hR
  exact hf.consequence (by
    rintro inp work out ⟨hc, hr, hv⟩
    refine ⟨hv.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work r items.length hv.eq_regT]
    simpa only [CurrentLoop.Invariant, accum_zero, List.take_zero, ReactionTraversal.code, output,
      List.flatMap_nil, List.append_nil, List.drop_zero, Nat.add_zero] using And.intro hc hr) (by
      intro inp work out hp
      have hout : clauses.take items.length = clauses := by rw [← hc, List.take_length]
      refine ⟨?_, ?_, hp.register⟩
      · simpa only [CurrentLoop.Invariant, List.take_length, hout, List.drop_length,
          ReactionTraversal.code, List.flatMap_nil, List.nil_append] using hp.on_work.1
      · simpa only [CurrentLoop.Invariant, accum_length] using hp.on_work.2) (runtime_bound L items.length hcount)

end JointThermoComplexity.Complexity.CurrentLoopEntry

#print axioms JointThermoComplexity.Complexity.CurrentLoopEntry.hoareTime
