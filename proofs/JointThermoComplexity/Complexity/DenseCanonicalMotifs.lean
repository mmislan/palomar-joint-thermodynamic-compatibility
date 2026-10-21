module
public import proofs.JointThermoComplexity.Complexity.DenseCanonicalBranch

set_option autoImplicit false
@[expose] public section

/-! Membership vectors encode exactly the two original supplied motifs.
The shared vertices, external catalysts and private vertices retain their numbering. -/

namespace JointThermoComplexity.Complexity.DenseCanonicalMotifs
open RationalLiteralNetwork DenseLiteralComplexCode
variable {e N : ℕ}

theorem image_membership {α β ι : Type} [Fintype ι] [DecidableEq β]
    (number : α ≃ β) (f : ι → α) (s : α) :
    number s ∈ Finset.univ.image (fun i => number (f i)) ↔ ∃ i, s = f i := by
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact ⟨i, (number.injective hi).symm⟩
  · rintro ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem left_species_mem (s : Species e N N) :
    speciesNumbering e N N s ∈ (leftMotif e N N).species ↔ ∃ i, s = leftVertex i :=
  image_membership (speciesNumbering e N N) leftVertex s

theorem right_species_mem (s : Species e N N) :
    speciesNumbering e N N s ∈ (rightMotif e N N).species ↔ ∃ i, s = rightVertex i :=
  image_membership (speciesNumbering e N N) rightVertex s

def leftSpeciesValues (e N : ℕ) : Fin (speciesCount e N N) → Bool :=
  Fin.append (fun _ => true) (Fin.append (fun _ : Fin e => false) (fun _ : Fin N => false))
def rightSpeciesValues (e N : ℕ) : Fin (speciesCount e N N) → Bool :=
  Fin.append (fun j : Fin (N + 2) => decide (j.val < 2))
    (Fin.append (fun _ : Fin e => false) (fun _ : Fin N => true))

theorem left_species_values :
    (fun s => decide (s ∈ (leftMotif e N N).species)) = leftSpeciesValues e N := by
  funext s
  obtain ⟨s, rfl⟩ := (speciesNumbering e N N).surjective s
  simp only [left_species_mem]
  cases s with
  | inl j => simp [leftSpeciesValues, number_left, Fin.append_left, leftVertex]
  | inr s =>
    cases s with
    | inl j => simp [leftSpeciesValues, number_external, Fin.append_right, Fin.append_left, leftVertex]
    | inr j => simp [leftSpeciesValues, number_private, Fin.append_right, leftVertex]

theorem right_species_values :
    (fun s => decide (s ∈ (rightMotif e N N).species)) = rightSpeciesValues e N := by
  funext s
  obtain ⟨s, rfl⟩ := (speciesNumbering e N N).surjective s
  simp only [right_species_mem]
  cases s with
  | inl j =>
    have hx : (∃ i : Fin (N + 2), (Sum.inl j : Species e N N) = rightVertex i) ↔ j.val < 2 := by
      simp only [right_vertex_left]
      exact ⟨fun h => h.choose_spec.1, fun h => ⟨j, h, rfl⟩⟩
    simp only [hx, rightSpeciesValues, number_left, Fin.append_left]
  | inr s =>
    cases s with
    | inl j => simp [rightSpeciesValues, number_external, Fin.append_right, Fin.append_left, right_vertex_external]
    | inr j =>
      have hx : ∃ i : Fin (N + 2), (Sum.inr (Sum.inr j) : Species e N N) = rightVertex i := by
        refine ⟨⟨2 + j.val, by have h := j.isLt; omega⟩, ?_⟩
        exact (right_vertex_private _ j).mpr rfl
      simp only [hx, decide_true, rightSpeciesValues, number_private, Fin.append_right]

def leftReactionValues (N : ℕ) : Fin (reactionCount N N) → Bool :=
  Fin.append (fun _ : Fin (N + 2) => true) (fun _ : Fin (N + 2) => false)
def rightReactionValues (N : ℕ) : Fin (reactionCount N N) → Bool :=
  Fin.append (fun _ : Fin (N + 2) => false) (fun _ : Fin (N + 2) => true)

theorem number_left_reaction (j : Fin (N + 2)) : reactionNumbering N N (.inl j) = Fin.castAdd (N + 2) j := rfl
theorem number_right_reaction (j : Fin (N + 2)) : reactionNumbering N N (.inr j) = Fin.natAdd (N + 2) j := rfl

theorem left_reactions_values :
    (fun r => decide (r ∈ (leftMotif e N N).reactions)) = leftReactionValues N := by
  funext r
  obtain ⟨r, rfl⟩ := (reactionNumbering N N).surjective r
  have hm : reactionNumbering N N r ∈ (leftMotif e N N).reactions ↔
      ∃ i : Fin (N + 2), r = Sum.inl i := image_membership (reactionNumbering N N) Sum.inl r
  simp only [hm]
  cases r with
  | inl j => simp [leftReactionValues, number_left_reaction, Fin.append_left]
  | inr j =>
    have hn : ¬ ∃ i : Fin (N + 2), (Sum.inr j : Reaction N N) = Sum.inl i := by simp
    simp only [hn, decide_false]
    change false = Fin.append (fun _ : Fin (N + 2) => true) (fun _ : Fin (N + 2) => false) (Fin.natAdd (N + 2) j)
    rw [Fin.append_right]

theorem right_reactions_values :
    (fun r => decide (r ∈ (rightMotif e N N).reactions)) = rightReactionValues N := by
  funext r
  obtain ⟨r, rfl⟩ := (reactionNumbering N N).surjective r
  have hm : reactionNumbering N N r ∈ (rightMotif e N N).reactions ↔
      ∃ i : Fin (N + 2), r = Sum.inr i := image_membership (reactionNumbering N N) Sum.inr r
  simp only [hm]
  cases r with
  | inl j => simp [rightReactionValues, number_left_reaction, Fin.append_left]
  | inr j =>
    have hx : ∃ i : Fin (N + 2), (Sum.inr j : Reaction N N) = Sum.inr i := ⟨j, rfl⟩
    simp only [hx, decide_true]
    change true = Fin.append (fun _ : Fin (N + 2) => false) (fun _ : Fin (N + 2) => true) (Fin.natAdd (N + 2) j)
    rw [Fin.append_right]

theorem constant_code {α : Type} (A : FiniteCodec.Codec α) (a : α) (k : ℕ) :
    FiniteCodec.functionCode A (fun _ : Fin k => a) = RepeatedOutput.copies (A.code a) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simpa only [FiniteCodec.functionCode_eq_flatMap, List.ofFn_succ_last, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, RepeatedOutput.copies] using
      congrArg (fun word => word ++ A.code a) ih

theorem finset_code {k : ℕ} (s : Finset (Fin k)) :
    (DataCodec.finset k).code s = FiniteCodec.functionCode FiniteCodec.boolean (fun j => decide (j ∈ s)) := rfl

theorem left_species_code : (DataCodec.finset (speciesCount e N N)).code (leftMotif e N N).species =
    RepeatedOutput.copies [true] (N + 2) ++ RepeatedOutput.copies [false] e ++ RepeatedOutput.copies [false] N := by
  rw [finset_code, left_species_values]
  unfold leftSpeciesValues speciesCount
  rw [DenseBlockWords.code_append, DenseBlockWords.code_append, constant_code, constant_code, constant_code]
  simp only [FiniteCodec.boolean, List.append_assoc]

theorem right_shared_code : FiniteCodec.functionCode FiniteCodec.boolean
    (fun j : Fin (N + 2) => decide (j.val < 2)) = [true, true] ++ RepeatedOutput.copies [false] N := by
  have hz : (fun j : Fin N => decide (j.succ.succ.val < 2)) = fun _ => false := by
    funext j
    simp only [Fin.val_succ]
    exact decide_eq_false (by omega)
  change [true] ++ ([true] ++ FiniteCodec.functionCode FiniteCodec.boolean
    (fun j : Fin N => decide (j.succ.succ.val < 2))) = _
  rw [hz, constant_code]
  rfl

theorem right_species_code : (DataCodec.finset (speciesCount e N N)).code (rightMotif e N N).species =
    [true, true] ++ RepeatedOutput.copies [false] N ++ RepeatedOutput.copies [false] e ++ RepeatedOutput.copies [true] N := by
  rw [finset_code, right_species_values]
  unfold rightSpeciesValues speciesCount
  rw [DenseBlockWords.code_append, DenseBlockWords.code_append, right_shared_code, constant_code, constant_code]
  simp only [FiniteCodec.boolean, List.append_assoc]

theorem left_reactions_code : (DataCodec.finset (reactionCount N N)).code (leftMotif e N N).reactions =
    RepeatedOutput.copies [true] (N + 2) ++ RepeatedOutput.copies [false] (N + 2) := by
  rw [finset_code, left_reactions_values]
  unfold leftReactionValues reactionCount
  rw [DenseBlockWords.code_append, constant_code, constant_code]
  rfl

theorem right_reactions_code : (DataCodec.finset (reactionCount N N)).code (rightMotif e N N).reactions =
    RepeatedOutput.copies [false] (N + 2) ++ RepeatedOutput.copies [true] (N + 2) := by
  rw [finset_code, right_reactions_values]
  unfold rightReactionValues reactionCount
  rw [DenseBlockWords.code_append, constant_code, constant_code]
  rfl

end JointThermoComplexity.Complexity.DenseCanonicalMotifs

#print axioms JointThermoComplexity.Complexity.DenseCanonicalMotifs.left_species_code
#print axioms JointThermoComplexity.Complexity.DenseCanonicalMotifs.right_species_code
#print axioms JointThermoComplexity.Complexity.DenseCanonicalMotifs.right_reactions_code
