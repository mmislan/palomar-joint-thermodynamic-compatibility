module
public import proofs.JointThermoComplexity.Complexity.MonomialCircuit

set_option autoImplicit false
@[expose] public section

/-! Prefix states and canonical exponent words for forward monomial traversal. -/

namespace JointThermoComplexity.Complexity.MonomialTraversal

variable {n : ℕ}

def code (items : List (Fin n × ℕ)) : List Bool := items.flatMap (fun item => BitCodec.naturalCode item.2)

def prefixState (s : MonomialCircuit.State n) (items : List (Fin n × ℕ)) (i : ℕ) : MonomialCircuit.State n :=
  s.runTerms (items.take i)

theorem run_append (s : MonomialCircuit.State n) (xs ys : List (Fin n × ℕ)) :
    s.runTerms (xs ++ ys) = (s.runTerms xs).runTerms ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons item items ih => exact ih (s.advance item)

theorem prefix_succ (s : MonomialCircuit.State n) (items : List (Fin n × ℕ)) (i : ℕ) (hi : i < items.length) :
    prefixState s items (i + 1) = (prefixState s items i).advance items[i] := by
  unfold prefixState
  rw [List.take_succ_eq_append_getElem hi, run_append]
  rfl

theorem prefix_le (s : MonomialCircuit.State n) (items : List (Fin n × ℕ)) (i : ℕ) :
    (prefixState s items i).size ≤ (s.runTerms items).size := by
  have hs := (prefixState s items i).runTerms_size_ge (items.drop i)
  simpa only [prefixState, ← run_append, List.take_append_drop] using hs

theorem code_take_succ (items : List (Fin n × ℕ)) (i : ℕ) (hi : i < items.length) :
    code (items.take (i + 1)) = code (items.take i) ++ BitCodec.naturalCode items[i].2 := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [code, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem code_drop_succ (items : List (Fin n × ℕ)) (i : ℕ) (hi : i < items.length) :
    code (items.drop i) = BitCodec.naturalCode items[i].2 ++ code (items.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem prefix_zero (s : MonomialCircuit.State n) (items : List (Fin n × ℕ)) : prefixState s items 0 = s := rfl

theorem prefix_length (s : MonomialCircuit.State n) (items : List (Fin n × ℕ)) :
    prefixState s items items.length = s.runTerms items := by simp only [prefixState, List.take_length]

end JointThermoComplexity.Complexity.MonomialTraversal

#print axioms JointThermoComplexity.Complexity.MonomialTraversal.prefix_le
