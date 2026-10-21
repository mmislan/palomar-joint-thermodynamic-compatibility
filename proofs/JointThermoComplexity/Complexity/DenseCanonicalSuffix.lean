module
public import proofs.JointThermoComplexity.Complexity.DenseCanonicalMotifs
public import proofs.JointThermoComplexity.Complexity.DenseNetworkSuffix

set_option autoImplicit false
@[expose] public section

/-! The actual fixed suffix is the original motif, direction and interval codec. -/

namespace JointThermoComplexity.Complexity.DenseCanonicalSuffix
open RationalLiteralNetwork RationalBranchData DenseCanonicalMotifs DenseLiteralComplexCode
variable {e N : ℕ}

theorem boxes_true_values : boxes true (e := e) (n := N) (m := N) =
    Fin.append (fun _ : Fin (N + 2) => some internalBox)
      (Fin.append (fun _ : Fin e => some externalBox) (fun _ : Fin N => some internalBox)) := by
  funext s
  obtain ⟨s, rfl⟩ := (speciesNumbering e N N).surjective s
  simp only [boxes, ite_true, Equiv.symm_apply_apply]
  cases s with
  | inl j => rw [number_left, Fin.append_left]
  | inr s =>
    cases s with
    | inl j => rw [number_external, Fin.append_right, Fin.append_left]
    | inr j => rw [number_private, Fin.append_right, Fin.append_right]

def boxWords (boxed : Bool) (e N : ℕ) : List Bool :=
  if boxed then RepeatedOutput.copies DenseNetworkSuffix.internalWord (N + 2) ++
    RepeatedOutput.copies DenseNetworkSuffix.externalWord e ++ RepeatedOutput.copies DenseNetworkSuffix.internalWord N
  else RepeatedOutput.copies [false] (speciesCount e N N)

theorem boxes_code (boxed : Bool) :
    FiniteCodec.functionCode (FiniteCodec.optional DataCodec.box) (boxes boxed (e := e) (n := N) (m := N)) = boxWords boxed e N := by
  cases boxed with
  | false => exact constant_code _ none _
  | true =>
    rw [boxes_true_values]
    change FiniteCodec.functionCode (FiniteCodec.optional DataCodec.box)
      (Fin.append (fun _ : Fin (N + 2) => some internalBox)
        (Fin.append (fun _ : Fin e => some externalBox) (fun _ : Fin N => some internalBox))) = _
    rw [DenseBlockWords.code_append, DenseBlockWords.code_append, constant_code, constant_code, constant_code]
    simp only [boxWords, ↓reduceIte, DenseNetworkSuffix.internalWord, DenseNetworkSuffix.externalWord, List.append_assoc]

def motifWords (e N : ℕ) : List Bool :=
  RepeatedOutput.copies [true] (N + 2) ++ RepeatedOutput.copies [false] e ++ RepeatedOutput.copies [false] N ++
    RepeatedOutput.copies [true] (N + 2) ++ RepeatedOutput.copies [false] (N + 2) ++
    [true, true] ++ RepeatedOutput.copies [false] N ++ RepeatedOutput.copies [false] e ++ RepeatedOutput.copies [true] N ++
    RepeatedOutput.copies [false] (N + 2) ++ RepeatedOutput.copies [true] (N + 2)

theorem motifs_code (boxed : Bool) (L R : Data (Fin e) N) :
    FiniteCodec.functionCode (DataCodec.motif (speciesCount e N N) (reactionCount N N)) (network boxed L R).motifs = motifWords e N := by
  change (((DataCodec.finset (speciesCount e N N)).code (leftMotif e N N).species ++
      (DataCodec.finset (reactionCount N N)).code (leftMotif e N N).reactions) ++
    (((DataCodec.finset (speciesCount e N N)).code (rightMotif e N N).species ++
      (DataCodec.finset (reactionCount N N)).code (rightMotif e N N).reactions) ++ [])) = _
  rw [left_species_code, left_reactions_code, right_species_code, right_reactions_code]
  simp only [motifWords, List.append_nil, List.append_assoc]

theorem forward_code (boxed : Bool) (L R : Data (Fin e) N) :
    FiniteCodec.functionCode FiniteCodec.boolean (network boxed L R).forward =
      RepeatedOutput.copies [true] (reactionCount N N) := constant_code _ true _

theorem word_explicit (boxed : Bool) (n N : ℕ) :
    DenseNetworkSuffix.word boxed n N = motifWords (DenseDimensionProgram.external boxed n) N ++
      RepeatedOutput.copies [true] (2 * N + 4) ++
      (if boxed then RepeatedOutput.copies DenseNetworkSuffix.internalWord (N + 2) ++
        RepeatedOutput.copies DenseNetworkSuffix.externalWord (DenseDimensionProgram.external boxed n) ++
        RepeatedOutput.copies DenseNetworkSuffix.internalWord N
      else RepeatedOutput.copies [false] (DenseDimensionProgram.external boxed n + 2 * N + 2)) := by
  cases boxed <;> simp [DenseNetworkSuffix.word, DenseNetworkSuffix.program, DenseNetworkSuffix.common,
    DenseNetworkSuffix.words, DenseNetworkSuffix.Part.word, DenseNetworkSuffix.values,
    DenseDimensionProgram.result, motifWords, List.append_assoc]

theorem tail_code (boxed : Bool) (n N : ℕ) (L R : Data (Fin (DenseDimensionProgram.external boxed n)) N) :
    DenseNetworkSuffix.word boxed n N =
      FiniteCodec.functionCode (DataCodec.motif (speciesCount (DenseDimensionProgram.external boxed n) N N) (reactionCount N N))
        (network boxed L R).motifs ++
      FiniteCodec.functionCode FiniteCodec.boolean (network boxed L R).forward ++
      FiniteCodec.functionCode (FiniteCodec.optional DataCodec.box) (network boxed L R).boxes := by
  change _ = _ ++ _ ++ FiniteCodec.functionCode (FiniteCodec.optional DataCodec.box) (boxes boxed)
  rw [motifs_code, forward_code, boxes_code, word_explicit]
  have hS : speciesCount (DenseDimensionProgram.external boxed n) N N = DenseDimensionProgram.external boxed n + 2 * N + 2 := by
    unfold speciesCount
    omega
  have hR : reactionCount N N = 2 * N + 4 := by unfold reactionCount; omega
  rw [hR]
  cases boxed <;> simp only [boxWords, Bool.false_eq_true, ↓reduceIte, hS]

end JointThermoComplexity.Complexity.DenseCanonicalSuffix

#print axioms JointThermoComplexity.Complexity.DenseCanonicalSuffix.boxes_code
#print axioms JointThermoComplexity.Complexity.DenseCanonicalSuffix.tail_code
