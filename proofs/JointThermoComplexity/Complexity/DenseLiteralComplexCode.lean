module
public import proofs.JointThermoComplexity.Complexity.DenseBlockWords
public import proofs.JointThermoComplexity.Complexity.RationalLiteralNetwork

set_option autoImplicit false
@[expose] public section

/-! Dense shared/external/private words are exactly the original literal complexes. -/

namespace JointThermoComplexity.Complexity.DenseLiteralComplexCode
open RationalLiteralNetwork RationalBranchData
variable {e N : ℕ}

theorem number_left (j : Fin (N + 2)) : speciesNumbering e N N (.inl j) = Fin.castAdd (e + N) j := rfl
theorem number_external (a : Fin e) : speciesNumbering e N N (.inr (.inl a)) = Fin.natAdd (N + 2) (Fin.castAdd N a) := rfl
theorem number_private (j : Fin N) : speciesNumbering e N N (.inr (.inr j)) = Fin.natAdd (N + 2) (Fin.natAdd e j) := rfl

theorem right_vertex_left (i j : Fin (N + 2)) :
    (Sum.inl j : Species e N N) = rightVertex i ↔ j.val < 2 ∧ j.val = i.val := by
  unfold rightVertex
  split_ifs with h0 h1
  · simp only [Sum.inl.injEq, Fin.ext_iff]
    omega
  · simp only [Sum.inl.injEq, Fin.ext_iff]
    omega
  · constructor
    · exact False.elim
    · intro h
      omega

theorem right_vertex_external (i : Fin (N + 2)) (a : Fin e) :
    (Sum.inr (Sum.inl a) : Species e N N) ≠ rightVertex i := by
  unfold rightVertex
  split_ifs <;> simp

theorem right_vertex_private (i : Fin (N + 2)) (j : Fin N) :
    (Sum.inr (Sum.inr j) : Species e N N) = rightVertex i ↔ 2 + j.val = i.val := by
  unfold rightVertex
  split_ifs with h0 h1
  · constructor
    · exact False.elim
    · intro h
      omega
  · constructor
    · exact False.elim
    · intro h
      omega
  · simp only [Sum.inr.injEq, Fin.ext_iff]
    omega

theorem left_values_raw (k : ℕ) (i : Fin (N + 2)) (γ : Fin e → ℕ) (s : Species e N N) :
    DenseBlockWords.leftValues k i.val N e γ (speciesNumbering e N N s) = atom (leftVertex i) k s + padding γ s := by
  cases s with
  | inl j =>
    rw [number_left]
    simp only [DenseBlockWords.leftValues, Fin.append_left, atom, leftVertex, padding,
      Sum.inl.injEq, Fin.ext_iff, Nat.add_zero]
  | inr s =>
    cases s with
    | inl a => simp [number_external, DenseBlockWords.leftValues, Fin.append_right, Fin.append_left, atom, leftVertex, padding]
    | inr j => simp [number_private, DenseBlockWords.leftValues, Fin.append_right, atom, leftVertex, padding]

theorem right_values_raw (k : ℕ) (i : Fin (N + 2)) (γ : Fin e → ℕ) (s : Species e N N) :
    DenseBlockWords.rightValues k i.val N e γ (speciesNumbering e N N s) = atom (rightVertex i) k s + padding γ s := by
  cases s with
  | inl j =>
    rw [number_left]
    simp only [DenseBlockWords.rightValues, Fin.append_left, atom, padding, right_vertex_left,
      Nat.add_zero, DenseBlockWords.rightShared]
    by_cases hj : j.val < 2 <;> by_cases hi : j.val = i.val <;> simp [hj, hi]
  | inr s =>
    cases s with
    | inl a => simp [number_external, DenseBlockWords.rightValues, Fin.append_right, Fin.append_left, atom, right_vertex_external, padding]
    | inr j =>
      rw [number_private]
      simp only [DenseBlockWords.rightValues, Fin.append_right, atom, padding, right_vertex_private, Nat.add_zero]

theorem left_atom_padding (k : ℕ) (i : Fin (N + 2)) (γ : Fin e → ℕ) :
    (fun s : Fin (speciesCount e N N) => atom (leftVertex i) k ((speciesNumbering e N N).symm s) +
      padding γ ((speciesNumbering e N N).symm s)) = DenseBlockWords.leftValues k i.val N e γ := by
  funext s
  obtain ⟨t, rfl⟩ := (speciesNumbering e N N).surjective s
  rw [Equiv.symm_apply_apply]
  exact (left_values_raw k i γ t).symm

theorem right_atom_padding (k : ℕ) (i : Fin (N + 2)) (γ : Fin e → ℕ) :
    (fun s : Fin (speciesCount e N N) => atom (rightVertex i) k ((speciesNumbering e N N).symm s) +
      padding γ ((speciesNumbering e N N).symm s)) = DenseBlockWords.rightValues k i.val N e γ := by
  funext s
  obtain ⟨t, rfl⟩ := (speciesNumbering e N N).surjective s
  rw [Equiv.symm_apply_apply]
  exact (right_values_raw k i γ t).symm

theorem left_reactant (L R : Data (Fin e) N) (i : Fin (N + 2)) :
    (reaction L R (reactionNumbering N N (.inl i))).reactant = DenseBlockWords.leftValues 1 i.val N e (L.powers i) := by
  change (fun s => reactantRaw L R ((reactionNumbering N N).symm (reactionNumbering N N (.inl i)))
    ((speciesNumbering e N N).symm s)) = _
  rw [Equiv.symm_apply_apply]
  exact left_atom_padding 1 i (L.powers i)

theorem right_reactant (L R : Data (Fin e) N) (i : Fin (N + 2)) :
    (reaction L R (reactionNumbering N N (.inr i))).reactant = DenseBlockWords.rightValues 1 i.val N e (R.powers i) := by
  change (fun s => reactantRaw L R ((reactionNumbering N N).symm (reactionNumbering N N (.inr i)))
    ((speciesNumbering e N N).symm s)) = _
  rw [Equiv.symm_apply_apply]
  exact right_atom_padding 1 i (R.powers i)

theorem left_product (L R : Data (Fin e) N) (i : Fin (N + 2)) :
    (reaction L R (reactionNumbering N N (.inl i))).product =
      DenseBlockWords.leftValues (gain N i) (finRotate (N + 2) i).val N e (L.powers i) := by
  change (fun s => productRaw L R ((reactionNumbering N N).symm (reactionNumbering N N (.inl i)))
    ((speciesNumbering e N N).symm s)) = _
  rw [Equiv.symm_apply_apply]
  exact left_atom_padding (gain N i) (finRotate (N + 2) i) (L.powers i)

theorem right_product (L R : Data (Fin e) N) (i : Fin (N + 2)) :
    (reaction L R (reactionNumbering N N (.inr i))).product =
      DenseBlockWords.rightValues (gain N i) (finRotate (N + 2) i).val N e (R.powers i) := by
  change (fun s => productRaw L R ((reactionNumbering N N).symm (reactionNumbering N N (.inr i)))
    ((speciesNumbering e N N).symm s)) = _
  rw [Equiv.symm_apply_apply]
  exact right_atom_padding (gain N i) (finRotate (N + 2) i) (R.powers i)

theorem left_reactant_code (L R : Data (Fin e) N) (i : Fin (N + 2)) :
    FiniteCodec.functionCode FiniteCodec.natural (reaction L R (reactionNumbering N N (.inl i))).reactant =
      DenseBlockWords.leftBefore 1 i.val N ++ FiniteCodec.functionCode FiniteCodec.natural (L.powers i) ++ DenseBlockWords.leftAfter N := by
  rw [left_reactant]
  exact (DenseBlockWords.left_full_code 1 i.val N e (L.powers i)).symm

theorem right_reactant_code (L R : Data (Fin e) N) (i : Fin (N + 2)) :
    FiniteCodec.functionCode FiniteCodec.natural (reaction L R (reactionNumbering N N (.inr i))).reactant =
      DenseBlockWords.rightBefore 1 i.val N ++ FiniteCodec.functionCode FiniteCodec.natural (R.powers i) ++ DenseBlockWords.rightAfter 1 i.val N := by
  rw [right_reactant]
  exact (DenseBlockWords.right_full_code 1 i.val N e (R.powers i)).symm

theorem left_product_code (L R : Data (Fin e) N) (i : Fin (N + 2)) :
    FiniteCodec.functionCode FiniteCodec.natural (reaction L R (reactionNumbering N N (.inl i))).product =
      DenseBlockWords.leftBefore (gain N i) (finRotate (N + 2) i).val N ++
        FiniteCodec.functionCode FiniteCodec.natural (L.powers i) ++ DenseBlockWords.leftAfter N := by
  rw [left_product]
  exact (DenseBlockWords.left_full_code (gain N i) (finRotate (N + 2) i).val N e (L.powers i)).symm

theorem right_product_code (L R : Data (Fin e) N) (i : Fin (N + 2)) :
    FiniteCodec.functionCode FiniteCodec.natural (reaction L R (reactionNumbering N N (.inr i))).product =
      DenseBlockWords.rightBefore (gain N i) (finRotate (N + 2) i).val N ++
        FiniteCodec.functionCode FiniteCodec.natural (R.powers i) ++ DenseBlockWords.rightAfter (gain N i) (finRotate (N + 2) i).val N := by
  rw [right_product]
  exact (DenseBlockWords.right_full_code (gain N i) (finRotate (N + 2) i).val N e (R.powers i)).symm

end JointThermoComplexity.Complexity.DenseLiteralComplexCode

#print axioms JointThermoComplexity.Complexity.DenseLiteralComplexCode.left_reactant_code
#print axioms JointThermoComplexity.Complexity.DenseLiteralComplexCode.right_reactant_code
#print axioms JointThermoComplexity.Complexity.DenseLiteralComplexCode.left_product_code
#print axioms JointThermoComplexity.Complexity.DenseLiteralComplexCode.right_product_code
