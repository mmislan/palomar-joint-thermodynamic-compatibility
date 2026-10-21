module
public import proofs.DInstabilityComplexity.PurePowerReduction

@[expose] public section

/-! # Evaluation correctness of the degree-decreasing numerator reduction -/

namespace DInstabilityComplexity.Separation

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def monomialValue (x : ι → ℝ) (m : ι →₀ ℕ) : ℝ := ∏ i, x i ^ m i

def smallMonomialValue (x : ι → ℝ) (b : SmallMonomial ι) : ℝ := ∏ i, x i ^ (b i).val

omit [DecidableEq ι] in
theorem monomialValue_add (x : ι → ℝ) (a b : ι →₀ ℕ) :
    monomialValue x (a + b) = monomialValue x a * monomialValue x b := by
  simp [monomialValue, pow_add, Finset.prod_mul_distrib]

theorem monomialValue_single (x : ι → ℝ) (i : ι) (n : ℕ) :
    monomialValue x (Finsupp.single i n) = x i ^ n := by
  simp [monomialValue, Finsupp.single_apply]

def numeratorEvaluation (f : Polynomial ℤ →+* ℝ) (x : ι → ℝ) :
    (SmallMonomial ι → Polynomial ℤ) →+ ℝ where
  toFun v := ∑ b, f (v b) * smallMonomialValue x b
  map_zero' := by simp
  map_add' u v := by simp [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem numeratorEvaluation_scale (f : Polynomial ℤ →+* ℝ) (x : ι → ℝ)
    (c : Polynomial ℤ) (v : SmallMonomial ι → Polynomial ℤ) :
    numeratorEvaluation f x (fun b => c * v b) = f c * numeratorEvaluation f x v := by
  simp only [numeratorEvaluation, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

omit [DecidableEq ι] in
theorem eval₂_as_small_support (f : Polynomial ℤ →+* ℝ) (x : ι → ℝ)
    (p : MvPolynomial ι (Polynomial ℤ)) :
    p.eval₂ f x = ∑ d : p.support, f (p.coeff d.val) * monomialValue x d.val := by
  exact (MvPolynomial.eval₂_eq' f x p).trans
    (Finset.sum_coe_sort p.support (fun d => f (p.coeff d) * monomialValue x d)).symm

omit [Fintype ι] in
theorem sub_five_add_single (m : ι →₀ ℕ) (i : ι) (hi : 5 ≤ m i) :
    m - Finsupp.single i 5 + Finsupp.single i 5 = m := by
  ext j
  by_cases hj : j = i
  · subst j
    simpa [Finsupp.tsub_apply] using Nat.sub_add_cancel hi
  · simp [hj]

/-- Correctness is uniform over every evaluation of the parameter ring and
every solution of the critical equations. The constructed numerators do not
depend on the point at which they are evaluated. -/
theorem reduceMonomial_evaluation (R : ι → MvPolynomial ι (Polynomial ℤ))
    (hR : ∀ i d, d ∈ (R i).support → monomialWeight d < 5)
    (D : Polynomial ℤ) (f : Polynomial ℤ →+* ℝ) (x : ι → ℝ)
    (hcritical : ∀ i, f D * x i ^ 5 = (R i).eval₂ f x) (m : ι →₀ ℕ) :
    numeratorEvaluation f x (reduceMonomial R hR D m) =
      f D ^ monomialWeight m * monomialValue x m := by
  classical
  induction m using (measure monomialWeight).wf.induction with
  | h m ih =>
    by_cases hm : ∀ i, m i < 5
    · rw [reduceMonomial, dite_eq_left hm]
      simp [numeratorEvaluation, apply_ite, smallMonomialValue, smallIndex, monomialValue]
    · let i := badIndex m hm
      let q := m - Finsupp.single i 5
      have hi : 5 ≤ m i := badIndex_ge m hm
      have hweight := monomialWeight_sub_five m i hi
      have hN : 0 < monomialWeight m := by omega
      have hdecomp : q + Finsupp.single i 5 = m := sub_five_add_single m i hi
      have hvalue : monomialValue x q * x i ^ 5 = monomialValue x m := by
        rw [← monomialValue_single, ← monomialValue_add, hdecomp]
      have hp : f D ^ (monomialWeight m - 1) * f D = f D ^ monomialWeight m := by
        rw [← pow_succ, Nat.sub_add_cancel hN]
      have hsum : numeratorEvaluation f x (reduceMonomial R hR D m) =
          ∑ d : (R i).support,
            f ((R i).coeff d.val) * f D ^
              (monomialWeight m - 1 - monomialWeight (q + d.val)) *
                numeratorEvaluation f x (reduceMonomial R hR D (q + d.val)) := by
        rw [reduceMonomial, dite_eq_right hm]
        simp only [map_sum, numeratorEvaluation_scale, map_mul, map_pow]
        rfl
      rw [hsum]
      calc
        (∑ d : (R i).support,
            f ((R i).coeff d.val) * f D ^
              (monomialWeight m - 1 - monomialWeight (q + d.val)) *
                numeratorEvaluation f x (reduceMonomial R hR D (q + d.val))) =
            ∑ d : (R i).support, f ((R i).coeff d.val) *
              f D ^ (monomialWeight m - 1) * monomialValue x (q + d.val) := by
          apply Finset.sum_congr rfl
          intro d _
          have hd : monomialWeight (q + d.val) < monomialWeight m :=
            substitution_degree_lt m i hi d.val (hR i d.val d.property)
          rw [ih (q + d.val) hd]
          have hp' : f D ^ (monomialWeight m - 1 - monomialWeight (q + d.val)) *
              f D ^ monomialWeight (q + d.val) = f D ^ (monomialWeight m - 1) := by
            rw [← pow_add, Nat.sub_add_cancel (by omega)]
          calc
            _ = f ((R i).coeff d.val) *
                (f D ^ (monomialWeight m - 1 - monomialWeight (q + d.val)) *
                  f D ^ monomialWeight (q + d.val)) * monomialValue x (q + d.val) := by ring
            _ = _ := by rw [hp']
        _ = f D ^ (monomialWeight m - 1) * monomialValue x q * (R i).eval₂ f x := by
          rw [eval₂_as_small_support, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d _
          rw [monomialValue_add]
          ring
        _ = f D ^ monomialWeight m * monomialValue x m := by
          rw [← hcritical i]
          calc
            _ = (f D ^ (monomialWeight m - 1) * f D) *
                (monomialValue x q * x i ^ 5) := by ring
            _ = _ := by rw [hp, hvalue]

#print axioms reduceMonomial_evaluation

end
end DInstabilityComplexity.Separation
