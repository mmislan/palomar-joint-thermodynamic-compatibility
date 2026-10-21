module
public import proofs.JointThermoComplexity.Complexity.SourceRawBounds
public import proofs.JointThermoComplexity.Complexity.NumericStrictData

set_option autoImplicit false
@[expose] public section

/-! # Raw coefficient bounds through the executable source pipeline

Homogenization preserves each retained coefficient. The exact scale and circle
equations introduce only fixed small coefficients. No cancellation is used in
any of these bounds.
-/

namespace JointThermoComplexity.Complexity.SparseRawPipelineBounds
open RealSyntax SparseInteger SourcePolynomialSchedules
variable {V A : Type}

theorem lift_term_weight (a : ℤ × List V) : rawWeight (SparseQuadraticLift.term a) ≤ a.1.natAbs := by
  unfold SparseQuadraticLift.term
  split <;> simp

theorem lift_weight (p : Poly V) : rawWeight (SparseQuadraticLift.lift p) ≤ rawWeight p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change rawWeight (SparseQuadraticLift.term a ++ SparseQuadraticLift.lift p) ≤ a.1.natAbs + rawWeight p
    rw [rawWeight_append]
    exact Nat.add_le_add (lift_term_weight a) ih

theorem chain_weight (m : ℕ) (j : Unit ⊕ Fin m) : rawWeight (SparseScaledSystem.chain m j) ≤ 5 := by
  cases j with
  | inl _ => simp [SparseScaledSystem.chain]
  | inr j => simp [SparseScaledSystem.chain]

theorem scaled_weight (q : A → Poly V) (B : ℕ) (hB : ∀ j, rawWeight (q j) ≤ B)
    (m : ℕ) (j : A ⊕ (Unit ⊕ Fin m)) : rawWeight (SparseScaledSystem.family q m j) ≤ max B 5 := by
  cases j with
  | inl j =>
    change rawWeight (relabel (ScaledQuadraticSystem.liftPorts m) (SparseQuadraticLift.lift (q j))) ≤ _
    rw [rawWeight_relabel]
    exact (lift_weight (q j)).trans ((hB j).trans (Nat.le_max_left _ _))
  | inr j =>
    change rawWeight (relabel (Sum.inr : Fin (m + 1) → V ⊕ Fin (m + 1)) (SparseScaledSystem.chain m j)) ≤ _
    rw [rawWeight_relabel]
    exact (chain_weight m j).trans (Nat.le_max_right _ _)

theorem circle_weight (i : V) : rawWeight (SparseCirclePadding.circle i) = 33 := by
  simp [SparseCirclePadding.circle]

theorem padded_weight (q : A → Poly V) (B : ℕ) (hB : ∀ j, rawWeight (q j) ≤ B) (j : A ⊕ V) :
    rawWeight (SparseCirclePadding.family q j) ≤ max B 33 := by
  cases j with
  | inl j =>
    change rawWeight (relabel (fun i => (i, false)) (q j)) ≤ _
    rw [rawWeight_relabel]
    exact (hB j).trans (Nat.le_max_left _ _)
  | inr i =>
    change rawWeight (SparseCirclePadding.circle i) ≤ _
    rw [circle_weight]
    exact Nat.le_max_right _ _

theorem numeric_original_length (s : Sentence) (j : SparseScaledSource.OriginalIndices s) :
    (SparseScaledSource.original s j).length ≤ 3 :=
  SparseCircuit.numeric_raw_term_count s _ (List.getElem_mem j.isLt)

theorem numeric_original_weight (s : Sentence) (j : SparseScaledSource.OriginalIndices s) :
    rawWeight (SparseScaledSource.original s j) ≤ 3 + 2 ^ s.code.length :=
  SparseCircuit.numeric_raw_weight s _ (List.getElem_mem j.isLt)

theorem numeric_padded_length (s : Sentence) (j : NumericStrictData.PaddedIndices s) :
    (NumericStrictData.paddedFamily s j).length ≤ 3 := by
  have hs (i : SparseScaledSource.Indices s (scaleLength s.code.length)) :
      (SparseScaledSource.family s (scaleLength s.code.length) i).length ≤ 3 :=
    SparseScaledSystem.family_length (SparseScaledSource.original s) 3 (numeric_original_length s) _ i
  exact SparseCirclePadding.family_length _ 3 hs j

theorem numeric_padded_weight (s : Sentence) (j : NumericStrictData.PaddedIndices s) :
    rawWeight (NumericStrictData.paddedFamily s j) ≤ 50 * 2 ^ s.code.length := by
  have hs (i : SparseScaledSource.Indices s (scaleLength s.code.length)) :
      rawWeight (SparseScaledSource.family s (scaleLength s.code.length) i) ≤ max (3 + 2 ^ s.code.length) 5 :=
    scaled_weight (SparseScaledSource.original s) _ (numeric_original_weight s) _ i
  have h := padded_weight (SparseScaledSource.family s (scaleLength s.code.length)) _ hs j
  have hpow : 1 ≤ 2 ^ s.code.length := Nat.one_le_two_pow
  exact h.trans (by omega)

theorem numeric_energy_length (s : Sentence) (j : Fin (NumericStrictData.paddedEquationCount s)) :
    (NumericStrictData.energyFamily s j).length ≤ 3 :=
  numeric_padded_length s ((NumericStrictData.paddedIndexEnumeration s).symm j)

theorem numeric_energy_weight (s : Sentence) (j : Fin (NumericStrictData.paddedEquationCount s)) :
    rawWeight (NumericStrictData.energyFamily s j) ≤ 50 * 2 ^ s.code.length :=
  numeric_padded_weight s ((NumericStrictData.paddedIndexEnumeration s).symm j)

end JointThermoComplexity.Complexity.SparseRawPipelineBounds

#print axioms JointThermoComplexity.Complexity.SparseRawPipelineBounds.lift_weight
#print axioms JointThermoComplexity.Complexity.SparseRawPipelineBounds.scaled_weight
#print axioms JointThermoComplexity.Complexity.SparseRawPipelineBounds.numeric_energy_length
#print axioms JointThermoComplexity.Complexity.SparseRawPipelineBounds.numeric_energy_weight
