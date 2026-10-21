module
public import proofs.JointThermoComplexity.Complexity.QuadraticHomogenization
public import proofs.JointThermoComplexity.Complexity.SourceCircuitWeight

set_option autoImplicit false
@[expose] public section

/-! # Coefficient-bit growth under the common quadratic lift -/

namespace JointThermoComplexity.Complexity.QuadraticHomogenization
open MvPolynomial SourceIntegerWeight DInstabilityComplexity.Separation RealSyntax QuadraticCircuit
variable {V : Type}

theorem component_weight_le (p : MvPolynomial V ℤ) (k : ℕ) :
    weight (homogeneousComponent k p) ≤ weight p := by
  classical
  have hs : (homogeneousComponent k p).support ⊆ p.support := by
    rw [support_homogeneousComponent]
    exact Finset.filter_subset _ _
  unfold weight
  rw [integerWeight.mvWeight_eq_sum _ p.support hs]
  change (∑ e ∈ p.support, ((homogeneousComponent k p).coeff e).natAbs) ≤
    ∑ e ∈ p.support, (p.coeff e).natAbs
  apply Finset.sum_le_sum
  intro e _
  rw [coeff_homogeneousComponent]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem weight_mul_X (p : MvPolynomial V ℤ) (v : V) : weight (p * X v) ≤ weight p := by
  simpa only [weight_X, Nat.mul_one] using weight_mul p (X v)

theorem weight_mul_X_sq (p : MvPolynomial V ℤ) (v : V) : weight (p * X v ^ 2) ≤ weight p := by
  calc
    weight (p * X v ^ 2) = weight ((p * X v) * X v) := by rw [pow_two, mul_assoc]
    _ ≤ weight (p * X v) := weight_mul_X _ _
    _ ≤ weight p := weight_mul_X _ _

theorem quadraticLift_weight_le (p : MvPolynomial V ℤ) :
    weight (quadraticLift p) ≤ 3 * weight p := by
  have hr (k : ℕ) : weight (rename (Sum.inl : V → V ⊕ Unit) (homogeneousComponent k p)) ≤ weight p :=
    (weight_rename _ _).trans (component_weight_le p k)
  have h0 : weight (rename (Sum.inl : V → V ⊕ Unit) (homogeneousComponent 0 p) * X (.inr ()) ^ 2) ≤ weight p :=
    (weight_mul_X_sq _ _).trans (hr 0)
  have h1 : weight (rename (Sum.inl : V → V ⊕ Unit) (homogeneousComponent 1 p) * X (.inr ())) ≤ weight p :=
    (weight_mul_X _ _).trans (hr 1)
  have h2 := hr 2
  unfold quadraticLift
  have hsum := weight_add
    (rename (Sum.inl : V → V ⊕ Unit) (homogeneousComponent 0 p) * X (.inr ()) ^ 2 +
      rename Sum.inl (homogeneousComponent 1 p) * X (.inr ()))
    (rename Sum.inl (homogeneousComponent 2 p))
  have hinner := weight_add
    (rename (Sum.inl : V → V ⊕ Unit) (homogeneousComponent 0 p) * X (.inr ()) ^ 2)
    (rename Sum.inl (homogeneousComponent 1 p) * X (.inr ()))
  omega

theorem quadraticLift_coeff_le (p : MvPolynomial V ℤ) (e : (V ⊕ Unit) →₀ ℕ) :
    ((quadraticLift p).coeff e).natAbs ≤ 3 * weight p :=
  (weight_coeff _ _).trans (quadraticLift_weight_le p)

theorem source_lift_coeff_bits_le (s : Sentence) (p : MvPolynomial (Fin (sourceArity s)) ℤ)
    (hp : p ∈ sourceEquations s) (e : (Fin (sourceArity s) ⊕ Unit) →₀ ℕ) :
    ((quadraticLift p).coeff e).natAbs.bits.length ≤ s.code.length + 4 := by
  have hweight := quadraticLift_coeff_le p e
  have hsource := sourceEquations_weight s p hp
  have hliteral := s.literalHeight_le_pow_code_length
  have hpowpos : 1 ≤ 2 ^ s.code.length := Nat.one_le_pow _ _ (by decide)
  have hpow : 2 ^ (s.code.length + 4) = 16 * 2 ^ s.code.length := by rw [pow_add]; ring
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  rw [hpow]
  omega

theorem source_lift_coeff_code_length_le (s : Sentence) (p : MvPolynomial (Fin (sourceArity s)) ℤ)
    (hp : p ∈ sourceEquations s) (e : (Fin (sourceArity s) ⊕ Unit) →₀ ℕ) :
    (BitCodec.integerCode ((quadraticLift p).coeff e)).length ≤ 2 * s.code.length + 10 := by
  rw [BitCodec.integerCode_length]
  have h := source_lift_coeff_bits_le s p hp e
  omega

theorem source_lift_coordinate_count_le (s : Sentence) :
    Fintype.card (Fin (sourceArity s) ⊕ Unit) ≤ 5 * s.code.length + 1 := by
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  exact Nat.add_le_add_right (sourceArity_le_code_length s) 1

end JointThermoComplexity.Complexity.QuadraticHomogenization

#print axioms JointThermoComplexity.Complexity.QuadraticHomogenization.quadraticLift_weight_le
#print axioms JointThermoComplexity.Complexity.QuadraticHomogenization.source_lift_coeff_code_length_le
#print axioms JointThermoComplexity.Complexity.QuadraticHomogenization.source_lift_coordinate_count_le
