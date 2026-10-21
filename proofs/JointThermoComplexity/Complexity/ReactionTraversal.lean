module
public import proofs.JointThermoComplexity.Complexity.NetworkCircuit
public import proofs.JointThermoComplexity.Complexity.DataCodec

set_option autoImplicit false
@[expose] public section

/-! Exact forward record words and prefix states for the actual network traversal. -/

namespace JointThermoComplexity.Complexity.ReactionTraversal

variable {n : ℕ}

def code (items : List (ReactionCircuit.Reaction n)) : List Bool := items.flatMap (DataCodec.reaction n).code

def prefixState (s : NetworkCircuit.State n) (items : List (ReactionCircuit.Reaction n)) (i : ℕ) : NetworkCircuit.State n :=
  s.run (items.take i)

theorem advance_size_ge (s : NetworkCircuit.State n) (q : ReactionCircuit.Reaction n) :
    s.size ≤ (s.advance q).size := ReactionCircuit.build_size_ge s.circuit q

theorem run_size_ge (s : NetworkCircuit.State n) (items : List (ReactionCircuit.Reaction n)) :
    s.size ≤ (s.run items).size := by
  induction items generalizing s with
  | nil => exact le_rfl
  | cons q qs ih => exact (advance_size_ge s q).trans (ih (s.advance q))

theorem run_append (s : NetworkCircuit.State n) (xs ys : List (ReactionCircuit.Reaction n)) :
    s.run (xs ++ ys) = (s.run xs).run ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons q qs ih => exact ih (s.advance q)

theorem prefix_succ (s : NetworkCircuit.State n) (items : List (ReactionCircuit.Reaction n)) (i : ℕ) (hi : i < items.length) :
    prefixState s items (i + 1) = (prefixState s items i).advance items[i] := by
  unfold prefixState
  rw [List.take_succ_eq_append_getElem hi, run_append]
  rfl

theorem prefix_le (s : NetworkCircuit.State n) (items : List (ReactionCircuit.Reaction n)) (i : ℕ) :
    (prefixState s items i).size ≤ (s.run items).size := by
  have hs := run_size_ge (prefixState s items i) (items.drop i)
  simpa only [prefixState, ← run_append, List.take_append_drop] using hs

theorem code_take_succ (items : List (ReactionCircuit.Reaction n)) (i : ℕ) (hi : i < items.length) :
    code (items.take (i + 1)) = code (items.take i) ++ (DataCodec.reaction n).code items[i] := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [code, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem code_drop_succ (items : List (ReactionCircuit.Reaction n)) (i : ℕ) (hi : i < items.length) :
    code (items.drop i) = (DataCodec.reaction n).code items[i] ++ code (items.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem prefix_zero (s : NetworkCircuit.State n) (items : List (ReactionCircuit.Reaction n)) : prefixState s items 0 = s := rfl

theorem prefix_length (s : NetworkCircuit.State n) (items : List (ReactionCircuit.Reaction n)) :
    prefixState s items items.length = s.run items := by simp only [prefixState, List.take_length]

end JointThermoComplexity.Complexity.ReactionTraversal

#print axioms JointThermoComplexity.Complexity.ReactionTraversal.prefix_le
