module
public import proofs.JointThermoComplexity.Complexity.SourceCoerciveMinimum

set_option autoImplicit false
@[expose] public section

/-! # An explicit global minimum gap for coercive quadratic sum-of-squares systems

The eliminant is constructed from the proved critical curve at one global
minimum. A nonzero minimum is separated from zero by an integer root bound.
The source reduction still has to establish the displayed coercivity premise
for its own emitted system and bound this height in terms of source bit length.
-/

namespace JointThermoComplexity.Complexity.SourceSeparation
open DInstabilityComplexity.Separation Filter
open scoped Topology
variable {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq ι]

noncomputable def minimumHeight (q : α → MvPolynomial ι ℤ) : ℕ :=
  (5 ^ Fintype.card ι).factorial *
    ((quadraticSquaredLength q + 1) * quadraticCriticalLength q ^
      (4 * Fintype.card ι + 4)) ^ (5 ^ Fintype.card ι)

theorem minimum_satisfies_bounded_integer_polynomial (q : α → MvPolynomial ι ℤ)
    (hq : ∀ j, (q j).totalDegree ≤ 2) (C : ℝ)
    (hc : ∀ x i, |x i| ≤ quadraticEnergy q x + C) :
    ∃ x₀ : ι → ℝ, (∀ y, quadraticEnergy q x₀ ≤ quadraticEnergy q y) ∧
      ∃ p : Polynomial ℤ, p ≠ 0 ∧
        p.eval₂ (Int.castRingHom ℝ) (quadraticEnergy q x₀) = 0 ∧
          ∀ j, (p.coeff j).natAbs ≤ minimumHeight q := by
  classical
  obtain ⟨x₀, z, t, hz, ht, hp, hcrit, hmin⟩ := exists_quadratic_critical_min_limit q C hc
  let R := quadraticRemainder q
  have hR : ∀ j d, d ∈ (R j).support → monomialWeight d < 5 :=
    fun j d hd => quadraticRemainder_support_degree_lt_five q hq j d hd
  let g := MvPolynomial.map Polynomial.C (quadraticEnergyPolynomial q)
  let L := 4 * Fintype.card ι + 4
  have hgdegree : g.totalDegree ≤ 4 := (totalDegree_map_le _ _).trans
    (quadraticEnergyPolynomial_totalDegree_le q hq)
  have hL : 4 * Fintype.card ι + g.totalDegree ≤ L := Nat.add_le_add_left hgdegree _
  have hglength : polynomialNumeratorLength g ≤ quadraticSquaredLength q := by
    rw [polynomialNumeratorLength_eq_mvWeight]
    exact (mapped_integer_mvWeight_le _).trans (quadraticEnergyPolynomial_integer_length_le q)
  let A := multiplicationMatrix R hR quadraticDenominator g L
  let Q := scaledEliminant A (quadraticDenominator ^ L)
  have hQ : Q ≠ 0 := scaledEliminant_ne_zero _ _ (pow_ne_zero _ quadraticDenominator_ne_zero)
  have hweight : twoVariableWeight Q ≤ minimumHeight q := by
    have hb := constructedEliminant_weight R hR quadraticDenominator g L (quadraticCriticalLength q)
      hL (quadraticDenominator_length_le q) (fun j => quadraticRemainder_length_le q hq j)
    exact hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right hglength 1)) _))
  have hu : Tendsto (fun n => quadraticEnergy q (z n)) atTop (𝓝 (quadraticEnergy q x₀)) :=
    (continuous_quadraticEnergy q).continuousAt.tendsto.comp hz
  have hroot (n : ℕ) : Q.eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (t n)) (quadraticEnergy q (z n)) = 0 := by
    have hb := constructedEliminant_root R hR quadraticDenominator g L hL
      (parameterEvaluation (t n)) (z n) (hcrit n)
    have heval : g.eval₂ (parameterEvaluation (t n)) (z n) = quadraticEnergy q (z n) := by
      rw [eval_map_parameter]
      rfl
    rw [heval] at hb
    exact hb
  obtain ⟨p, hp0, hproot, hpcoeff⟩ := integer_polynomial_of_limiting_curve Q hQ t
    (fun n => quadraticEnergy q (z n)) (quadraticEnergy q x₀)
    (fun n => ne_of_gt (hp n)) ht hu hroot
  exact ⟨x₀, hmin, p, hp0, hproot, fun j => (hpcoeff j).trans hweight⟩

theorem coercive_quadratic_energy_gap (q : α → MvPolynomial ι ℤ)
    (hq : ∀ j, (q j).totalDegree ≤ 2) (C : ℝ)
    (hc : ∀ x i, |x i| ≤ quadraticEnergy q x + C)
    (hno : ¬ ∃ x : ι → ℝ, ∀ j, (q j).eval₂ (Int.castRingHom ℝ) x = 0) :
    ∀ x, 1 / ((minimumHeight q : ℝ) + 1) < quadraticEnergy q x := by
  obtain ⟨x₀, hmin, p, hp, hroot, hcoeff⟩ := minimum_satisfies_bounded_integer_polynomial q hq C hc
  have hnonzero : quadraticEnergy q x₀ ≠ 0 := by
    intro hz
    exact hno ⟨x₀, (quadraticEnergy_eq_zero_iff q x₀).mp hz⟩
  have hcoeffInt (j : ℕ) : |p.coeff j| ≤ (minimumHeight q : ℤ) := by
    have h : ((p.coeff j).natAbs : ℤ) ≤ (minimumHeight q : ℤ) := by exact_mod_cast hcoeff j
    simpa only [Int.natCast_natAbs] using h
  have hgap := integer_root_abs_gt p hp (minimumHeight q) hcoeffInt
    (quadraticEnergy q x₀) hnonzero hroot
  rw [abs_of_nonneg (quadraticEnergy_nonneg q x₀)] at hgap
  exact fun x => hgap.trans_le (hmin x)

end JointThermoComplexity.Complexity.SourceSeparation

#print axioms JointThermoComplexity.Complexity.SourceSeparation.minimum_satisfies_bounded_integer_polynomial
#print axioms JointThermoComplexity.Complexity.SourceSeparation.coercive_quadratic_energy_gap
