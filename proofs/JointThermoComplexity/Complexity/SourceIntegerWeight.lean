module
public import proofs.DInstabilityComplexity.MvPolynomialWeight

set_option autoImplicit false
@[expose] public section

/-! # Integer coefficient weights under arbitrary coordinate renaming

This extends the authenticated algebraic coefficient-weight library without
replaying it. In particular, coordinate collisions can only reduce the bound.
-/

namespace JointThermoComplexity.Complexity.SourceIntegerWeight
open MvPolynomial DInstabilityComplexity.Separation
variable {V W : Type}

noncomputable def weight (p : MvPolynomial V ℤ) : ℕ := integerWeight.mvWeight p

theorem weight_coeff (p : MvPolynomial V ℤ) (d : V →₀ ℕ) :
    (p.coeff d).natAbs ≤ weight p := by
  classical
  by_cases hd : d ∈ p.support
  · change (p.coeff d).natAbs ≤ ∑ e ∈ p.support, (p.coeff e).natAbs
    exact Finset.single_le_sum (f := fun e => (p.coeff e).natAbs) (fun _ _ => Nat.zero_le _) hd
  · simp [MvPolynomial.notMem_support_iff.mp hd]

theorem weight_monomial (d : V →₀ ℕ) (z : ℤ) : weight (monomial d z) = z.natAbs :=
  integerWeight.mvWeight_monomial d z

@[simp] theorem weight_X (v : V) : weight (X v) = 1 := weight_monomial _ _

@[simp] theorem weight_C (z : ℤ) : weight (C (σ := V) z) = z.natAbs :=
  integerWeight.mvWeight_C z

@[simp] theorem weight_one : weight (1 : MvPolynomial V ℤ) = 1 :=
  integerWeight.mvWeight_one

theorem weight_add (p q : MvPolynomial V ℤ) : weight (p + q) ≤ weight p + weight q :=
  integerWeight.mvWeight_add_le p q

theorem weight_sub (p q : MvPolynomial V ℤ) : weight (p - q) ≤ weight p + weight q := by
  simpa only [sub_eq_add_neg, weight, integerWeight.mvWeight_neg] using weight_add p (-q)

theorem weight_mul (p q : MvPolynomial V ℤ) : weight (p * q) ≤ weight p * weight q :=
  integerWeight.mvWeight_mul_le p q

theorem weight_rename (f : V → W) (p : MvPolynomial V ℤ) :
    weight (rename f p) ≤ weight p := by
  classical
  have he : rename f p = ∑ d ∈ p.support, monomial (d.mapDomain f) (p.coeff d) := by
    conv_lhs => rw [MvPolynomial.as_sum p]
    simp only [map_sum, MvPolynomial.rename_monomial]
  rw [he]
  exact (integerWeight.mvWeight_sum_le _ _).trans (by
    simp only [integerWeight.mvWeight_monomial]; exact le_rfl)

theorem weight_X_sub_X (v w : V) : weight (X v - X w) ≤ 2 := by
  simpa only [weight_X] using weight_sub (X v : MvPolynomial V ℤ) (X w)

theorem weight_X_add_X (v w : V) : weight (X v + X w) ≤ 2 := by
  simpa only [weight_X] using weight_add (X v : MvPolynomial V ℤ) (X w)

theorem weight_X_sub_one (v : V) : weight (X v - 1) ≤ 2 := by
  simpa only [weight_X, weight_one] using weight_sub (X v : MvPolynomial V ℤ) 1

theorem weight_boolean (v : V) : weight (X v * (X v - 1)) ≤ 2 := by
  exact (weight_mul _ _).trans (by simpa only [weight_X, one_mul] using weight_X_sub_one v)

theorem weight_X_sub_add (u v w : V) : weight (X u - (X v + X w)) ≤ 3 := by
  have h := weight_sub (X u : MvPolynomial V ℤ) (X v + X w)
  simp only [weight_X] at h
  exact h.trans (Nat.add_le_add_left (weight_X_add_X v w) 1)

theorem weight_add_sub_X (u v w : V) : weight (X u + X v - X w) ≤ 3 := by
  have h := weight_sub (X u + X v : MvPolynomial V ℤ) (X w)
  simp only [weight_X] at h
  exact h.trans (Nat.add_le_add_right (weight_X_add_X u v) 1)

theorem weight_X_sub_mul (u v w : V) : weight (X u - X v * X w) ≤ 2 := by
  have h := weight_sub (X u : MvPolynomial V ℤ) (X v * X w)
  have hm := weight_mul (X v : MvPolynomial V ℤ) (X w)
  simp only [weight_X] at h hm
  omega

theorem weight_X_sub_sq (u v : V) : weight (X u - X v ^ 2) ≤ 2 := by
  simpa only [pow_two] using weight_X_sub_mul u v v

theorem weight_X_sub_difference_mul (u v w z : V) :
    weight (X u - (X v - X w) * X z) ≤ 3 := by
  have h := weight_sub (X u : MvPolynomial V ℤ) ((X v - X w) * X z)
  have hm := weight_mul (X v - X w : MvPolynomial V ℤ) (X z)
  have hd := weight_X_sub_X v w
  simp only [weight_X, mul_one] at h hm
  omega

theorem weight_X_mul_difference (u v w : V) : weight (X u * (X v - X w)) ≤ 2 := by
  exact (weight_mul _ _).trans (by simpa only [weight_X, one_mul] using weight_X_sub_X v w)

end JointThermoComplexity.Complexity.SourceIntegerWeight

#print axioms JointThermoComplexity.Complexity.SourceIntegerWeight.weight_coeff
#print axioms JointThermoComplexity.Complexity.SourceIntegerWeight.weight_rename
