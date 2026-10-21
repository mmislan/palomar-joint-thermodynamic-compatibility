module
public import proofs.DInstabilityComplexity.PolynomialWeight
public import proofs.DInstabilityComplexity.GradientBounds
public import proofs.DInstabilityComplexity.EliminationMatrix

@[expose] public section

/-! # Multivariate coefficient lengths and differentiation bounds -/

namespace DInstabilityComplexity.Separation

noncomputable section

namespace NatRingWeight

variable {S : Type*} [CommRing S] (W : NatRingWeight S)

theorem natCast_le (n : ℕ) : W (n : S) ≤ n := by
  induction n with
  | zero => simp [W.zero_eq]
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (W.add_le _ _).trans (by simpa only [W.one_eq] using Nat.add_le_add_right ih 1)

def mvWeight (p : MvPolynomial ι S) : ℕ := ∑ d ∈ p.support, W (p.coeff d)

theorem mvWeight_eq_sum (p : MvPolynomial ι S) (s : Finset (ι →₀ ℕ)) (hs : p.support ⊆ s) :
    W.mvWeight p = ∑ d ∈ s, W (p.coeff d) := by
  classical
  apply Finset.sum_subset hs
  intro d _ hd
  rw [MvPolynomial.notMem_support_iff.mp hd, W.zero_eq]

theorem mvWeight_zero : W.mvWeight (0 : MvPolynomial ι S) = 0 := by simp [mvWeight]

theorem mvWeight_monomial (d : ι →₀ ℕ) (a : S) :
    W.mvWeight (MvPolynomial.monomial d a) = W a := by
  classical
  by_cases ha : a = 0
  · simp [ha, mvWeight_zero, W.zero_eq]
  · simp [mvWeight, MvPolynomial.support_monomial, ha]

theorem mvWeight_C (a : S) : W.mvWeight (MvPolynomial.C (σ := ι) a) = W a :=
  W.mvWeight_monomial 0 a

theorem mvWeight_one : W.mvWeight (1 : MvPolynomial ι S) = 1 := by
  simpa only [map_one] using (W.mvWeight_C (ι := ι) (1 : S)).trans W.one_eq

theorem mvWeight_neg (p : MvPolynomial ι S) : W.mvWeight (-p) = W.mvWeight p := by
  simp only [mvWeight, MvPolynomial.support_neg, MvPolynomial.coeff_neg, W.neg_eq]

theorem mvWeight_add_le (p q : MvPolynomial ι S) :
    W.mvWeight (p + q) ≤ W.mvWeight p + W.mvWeight q := by
  classical
  let T := p.support ∪ q.support
  calc
    W.mvWeight (p + q) = ∑ d ∈ T, W ((p + q).coeff d) :=
      W.mvWeight_eq_sum _ _ MvPolynomial.support_add
    _ ≤ ∑ d ∈ T, (W (p.coeff d) + W (q.coeff d)) := by
      apply Finset.sum_le_sum
      intro d _
      rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      exact W.add_le _ _
    _ = W.mvWeight p + W.mvWeight q := by
      rw [Finset.sum_add_distrib,
        ← W.mvWeight_eq_sum p T Finset.subset_union_left,
        ← W.mvWeight_eq_sum q T Finset.subset_union_right]

theorem mvWeight_sum_le (s : Finset α) (p : α → MvPolynomial ι S) :
    W.mvWeight (∑ a ∈ s, p a) ≤ ∑ a ∈ s, W.mvWeight (p a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mvWeight_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (W.mvWeight_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem mvWeight_mul_le (p q : MvPolynomial ι S) :
    W.mvWeight (p * q) ≤ W.mvWeight p * W.mvWeight q := by
  classical
  have he : p * q = ∑ d ∈ p.support, ∑ e ∈ q.support,
      MvPolynomial.monomial (d + e) (p.coeff d * q.coeff e) := by
    calc
      p * q = (∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d)) *
          (∑ e ∈ q.support, MvPolynomial.monomial e (q.coeff e)) :=
        congrArg₂ (· * ·) (MvPolynomial.as_sum p) (MvPolynomial.as_sum q)
      _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum, MvPolynomial.monomial_mul_monomial]
        rw [Finset.sum_comm]
  rw [he]
  calc
    W.mvWeight (∑ d ∈ p.support, ∑ e ∈ q.support,
        MvPolynomial.monomial (d + e) (p.coeff d * q.coeff e)) ≤
        ∑ d ∈ p.support, W.mvWeight (∑ e ∈ q.support,
          MvPolynomial.monomial (d + e) (p.coeff d * q.coeff e)) := W.mvWeight_sum_le _ _
    _ ≤ ∑ d ∈ p.support, ∑ e ∈ q.support,
        W.mvWeight (MvPolynomial.monomial (d + e) (p.coeff d * q.coeff e)) := by
      apply Finset.sum_le_sum
      intro d _
      exact W.mvWeight_sum_le _ _
    _ = ∑ d ∈ p.support, ∑ e ∈ q.support, W (p.coeff d * q.coeff e) := by
      simp only [mvWeight_monomial]
    _ ≤ ∑ d ∈ p.support, ∑ e ∈ q.support, W (p.coeff d) * W (q.coeff e) :=
      Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => W.mul_le _ _
    _ = W.mvWeight p * W.mvWeight q := by
      simp only [mvWeight]
      rw [Finset.sum_mul_sum]

def mvLift : NatRingWeight (MvPolynomial ι S) where
  weight := W.mvWeight
  zero_eq := W.mvWeight_zero
  one_eq := W.mvWeight_one
  neg_eq := W.mvWeight_neg
  add_le := W.mvWeight_add_le
  mul_le := W.mvWeight_mul_le

theorem mvWeight_map_le {R : Type*} [CommRing R] (V : NatRingWeight R)
    (f : R →+* S) (hf : ∀ a, W (f a) ≤ V a) (p : MvPolynomial ι R) :
    W.mvWeight (MvPolynomial.map f p) ≤ V.mvWeight p := by
  classical
  rw [W.mvWeight_eq_sum _ p.support (MvPolynomial.support_map_subset f p)]
  simp only [MvPolynomial.coeff_map]
  exact Finset.sum_le_sum fun _ _ => hf _

theorem mvWeight_pderiv_le (p : MvPolynomial ι S) (i : ι) :
    W.mvWeight (MvPolynomial.pderiv i p) ≤ p.totalDegree * W.mvWeight p := by
  classical
  have he : MvPolynomial.pderiv i p = ∑ d ∈ p.support,
      MvPolynomial.monomial (d - Finsupp.single i 1) (p.coeff d * (d i : S)) := by
    conv_lhs => rw [MvPolynomial.as_sum p]
    simp only [map_sum, MvPolynomial.pderiv_monomial]
  rw [he]
  calc
    W.mvWeight (∑ d ∈ p.support,
        MvPolynomial.monomial (d - Finsupp.single i 1) (p.coeff d * (d i : S))) ≤
        ∑ d ∈ p.support, W.mvWeight
          (MvPolynomial.monomial (d - Finsupp.single i 1) (p.coeff d * (d i : S))) := W.mvWeight_sum_le _ _
    _ = ∑ d ∈ p.support, W (p.coeff d * (d i : S)) := by simp only [mvWeight_monomial]
    _ ≤ ∑ d ∈ p.support, W (p.coeff d) * p.totalDegree := by
      apply Finset.sum_le_sum
      intro d hd
      have hdi : d i ≤ p.totalDegree :=
        (MvPolynomial.le_degreeOf_of_mem_support i hd).trans (MvPolynomial.degreeOf_le_totalDegree p i)
      exact (W.mul_le _ _).trans (Nat.mul_le_mul_left _ ((W.natCast_le _).trans hdi))
    _ = p.totalDegree * W.mvWeight p := by
      rw [← Finset.sum_mul]
      exact Nat.mul_comm _ _

end NatRingWeight

def integerWeight : NatRingWeight ℤ where
  weight := Int.natAbs
  zero_eq := by decide
  one_eq := by decide
  neg_eq := Int.natAbs_neg
  add_le := Int.natAbs_add_le
  mul_le := fun a b => le_of_eq (Int.natAbs_mul a b)

theorem polynomialNumeratorLength_eq_mvWeight (p : MvPolynomial ι (Polynomial ℤ)) :
    polynomialNumeratorLength p = integerPolynomialWeight.mvWeight p := by
  exact Finset.sum_coe_sort p.support (fun d => coefficientLength (p.coeff d))

theorem mapped_integer_mvWeight_le (p : MvPolynomial ι ℤ) :
    integerPolynomialWeight.mvWeight (MvPolynomial.map Polynomial.C p) ≤ integerWeight.mvWeight p := by
  apply integerPolynomialWeight.mvWeight_map_le integerWeight Polynomial.C
  intro z
  exact le_of_eq (coefficientLength_monomial 0 z)

#print axioms NatRingWeight.mvWeight_pderiv_le
#print axioms mapped_integer_mvWeight_le

end
end DInstabilityComplexity.Separation
