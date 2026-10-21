module
public import proofs.JointThermoComplexity.Complexity.ReactionTraversal
public import proofs.JointThermoComplexity.Complexity.ReactionBuildCode

set_option autoImplicit false
@[expose] public section

/-! Each retained reaction output is the last gate of its own forward circuit prefix. -/

namespace JointThermoComplexity.Complexity.NetworkOutputAddress

variable {n r : ℕ}

def numbers (s : NetworkCircuit.State n) : List ℕ := s.outputs.map Fin.val

def emitted (start : ℕ) : List (ReactionCircuit.Reaction n) → List ℕ
  | [] => []
  | q :: qs => (start + ExactGateCount.reactionCost q - 1) :: emitted (start + ExactGateCount.reactionCost q) qs

theorem reaction_last {k : ℕ} (c : RealCircuit.Circuit n k) (q : ReactionCircuit.Reaction n) :
    (ReactionCircuit.build c q).output.val + 1 = (ReactionCircuit.build c q).size := by
  rw [ReactionBuildCode.output_value, ReactionBuildCode.size]

theorem advance_numbers (s : NetworkCircuit.State n) (q : ReactionCircuit.Reaction n) :
    numbers (s.advance q) = numbers s ++ [s.size + ExactGateCount.reactionCost q - 1] := by
  have hs := ExactGateCount.reaction_size s.circuit q
  have ho := reaction_last s.circuit q
  have hv : (ReactionCircuit.build s.circuit q).output.val = s.size + ExactGateCount.reactionCost q - 1 := by omega
  simp only [numbers, NetworkCircuit.State.advance, List.map_append, List.map_map, List.map_cons,
    List.map_nil, Function.comp_def, Fin.val_castLE, hv]

theorem run_numbers (s : NetworkCircuit.State n) (items : List (ReactionCircuit.Reaction n)) :
    numbers (s.run items) = numbers s ++ emitted s.size items := by
  induction items generalizing s with
  | nil => simp only [NetworkCircuit.State.run, emitted, List.append_nil]
  | cons q qs ih =>
    rw [NetworkCircuit.State.run, ih, advance_numbers, ExactGateCount.network_advance_size]
    simp only [emitted, List.append_assoc, List.singleton_append]

theorem emitted_at (start : ℕ) (items : List (ReactionCircuit.Reaction n)) (i : ℕ) (hi : i < items.length) :
    (emitted start items)[i]? = some (start + ExactGateCount.networkCost (items.take (i + 1)) - 1) := by
  induction items generalizing start i with
  | nil => simp at hi
  | cons q qs ih =>
    cases i with
    | zero => simp only [emitted, List.getElem?_cons_zero, List.take_succ_cons, List.take_zero,
        ExactGateCount.networkCost, Nat.add_zero]
    | succ i =>
      rw [emitted, List.getElem?_cons_succ, ih _ i (by simp only [List.length_cons] at hi; omega)]
      simp only [List.take_succ_cons, ExactGateCount.networkCost, Nat.add_assoc]

theorem dense_output (qs : Fin r → ReactionCircuit.Reaction n) (i : Fin r) :
    (NetworkCircuit.output qs i).val = ExactGateCount.networkCost ((List.ofFn qs).take (i.val + 1)) - 1 := by
  have hn := run_numbers (⟨0, .nil, []⟩ : NetworkCircuit.State n) (List.ofFn qs)
  have hi : i.val < (NetworkCircuit.dense qs).outputs.length := by
    rw [NetworkCircuit.dense, NetworkCircuit.build_length, List.length_ofFn]
    exact i.isLt
  have hv := congrArg (fun xs : List ℕ => xs[i.val]?) hn
  have he := emitted_at 0 (List.ofFn qs) i.val (by simpa only [List.length_ofFn] using i.isLt)
  change (numbers (NetworkCircuit.dense qs))[i.val]? = ([] ++ emitted 0 (List.ofFn qs))[i.val]? at hv
  rw [List.nil_append, he] at hv
  simpa only [numbers, List.getElem?_map, List.getElem?_eq_getElem hi, Option.map_some,
    Option.some.injEq, Nat.zero_add, NetworkCircuit.output] using hv

end JointThermoComplexity.Complexity.NetworkOutputAddress

#print axioms JointThermoComplexity.Complexity.NetworkOutputAddress.dense_output
