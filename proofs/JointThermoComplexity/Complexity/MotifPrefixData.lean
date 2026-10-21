module
public import proofs.JointThermoComplexity.Complexity.MotifPrefixSkip
public import proofs.JointThermoComplexity.Complexity.MotifAccess

set_option autoImplicit false
@[expose] public section

/-! Exact original-input motif prefixes and suffixes at any actual core position, including the final count. -/

namespace JointThermoComplexity.Complexity.MotifPrefixData
open MotifPrefixSkip

def items (Q : NetworkCodec.Input) : List (NetworkData.Motif Q.speciesCount Q.reactionCount) := List.ofFn Q.network.motifs

def wordPrefix (Q : NetworkCodec.Input) (ci : ℕ) : List Bool := code ((items Q).take ci)

def before (Q : NetworkCodec.Input) (ci : ℕ) : List Bool := MotifAccess.before Q ++ wordPrefix Q ci

def remaining (Q : NetworkCodec.Input) (ci : ℕ) : List Bool :=
  code ((items Q).drop ci) ++ (BoxTraversalData.forward Q ++ BoxTraversalData.boxes Q)

theorem items_length (Q : NetworkCodec.Input) : (items Q).length = Q.coreCount := by simp only [items, List.length_ofFn]

theorem prefix_count (Q : NetworkCodec.Input) (ci : ℕ) (hci : ci ≤ Q.coreCount) : ((items Q).take ci).length = ci := by
  rw [List.length_take, items_length, Nat.min_eq_left hci]

theorem code_eq (Q : NetworkCodec.Input) : code (items Q) = FixedWordsSkip.code (BoxTraversalData.motifs Q) := by
  change (List.ofFn Q.network.motifs).flatMap (DataCodec.motif Q.speciesCount Q.reactionCount).code =
    (List.ofFn ((DataCodec.motif Q.speciesCount Q.reactionCount).code ∘ Q.network.motifs)).flatMap id
  rw [← List.map_ofFn, List.flatMap_map]
  rfl

theorem tail_split (Q : NetworkCodec.Input) (ci : ℕ) : NetworkTallyData.tail Q = wordPrefix Q ci ++ remaining Q ci := by
  rw [BoxTraversalData.tail_split, ← code_eq]
  have h := congrArg code (List.take_append_drop ci (items Q))
  rw [code_append] at h
  calc code (items Q) ++ (BoxTraversalData.forward Q ++ BoxTraversalData.boxes Q) =
      (code ((items Q).take ci) ++ code ((items Q).drop ci)) ++
        (BoxTraversalData.forward Q ++ BoxTraversalData.boxes Q) := by rw [h]
      _ = _ := List.append_assoc _ _ _

theorem input_split (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q) (ci : ℕ) :
    before Q ci ++ remaining Q ci = input := by
  rw [before, List.append_assoc, ← tail_split]
  simpa only [MotifAccess.before, List.append_assoc] using (MotifAccess.input_split input Q hd).symm

theorem first_before (Q : NetworkCodec.Input) : before Q 0 = MotifAccess.before Q := by
  simp only [before, wordPrefix, List.take_zero, code, List.flatMap_nil, List.append_nil]

theorem first_remaining (Q : NetworkCodec.Input) : remaining Q 0 = NetworkTallyData.tail Q := by
  rw [tail_split Q 0]
  simp only [wordPrefix, List.take_zero, code, List.flatMap_nil, List.nil_append]

theorem remaining_at (Q : NetworkCodec.Input) (a : Fin Q.coreCount) :
    remaining Q a.val = (DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a) ++ remaining Q (a.val + 1) := by
  unfold remaining
  rw [code_drop_succ (items Q) a.val (by rw [items_length]; exact a.isLt)]
  simp only [items, List.getElem_ofFn, List.append_assoc]

theorem before_succ (Q : NetworkCodec.Input) (a : Fin Q.coreCount) :
    before Q (a.val + 1) = before Q a.val ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a) := by
  unfold before wordPrefix
  rw [code_take_succ (items Q) a.val (by rw [items_length]; exact a.isLt)]
  simp only [items, List.getElem_ofFn, List.append_assoc]

end JointThermoComplexity.Complexity.MotifPrefixData

#print axioms JointThermoComplexity.Complexity.MotifPrefixData.input_split
#print axioms JointThermoComplexity.Complexity.MotifPrefixData.remaining_at
#print axioms JointThermoComplexity.Complexity.MotifPrefixData.before_succ
