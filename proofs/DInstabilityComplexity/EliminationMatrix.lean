module
public import proofs.DInstabilityComplexity.PurePowerEvaluation
public import proofs.DInstabilityComplexity.PurePowerLength

@[expose] public section

/-!
# A uniformly scaled multiplication matrix

Rows represent multiplication by the objective in the bounded monomial basis.
The entries are integer polynomials in the parameter, constructed by the proved
reductor. Evaluation gives an actual eigenvector, with coefficient lengths
controlled uniformly before any parameter or critical point is chosen.
-/

namespace DInstabilityComplexity.Separation

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def smallExponent (b : SmallMonomial ι) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (b i).val

omit [DecidableEq ι] in
theorem monomialValue_smallExponent (x : ι → ℝ) (b : SmallMonomial ι) :
    monomialValue x (smallExponent b) = smallMonomialValue x b := rfl

omit [DecidableEq ι] in
theorem smallExponent_weight_le (b : SmallMonomial ι) :
    monomialWeight (smallExponent b) ≤ 4 * Fintype.card ι := by
  have he : monomialWeight (smallExponent b) = ∑ i, (b i).val :=
    Finsupp.equivFunOnFinite_symm_sum _
  rw [he]
  exact smallMonomial_weight_le b

omit [DecidableEq ι] in
theorem productExponent_weight_le (g : MvPolynomial ι (Polynomial ℤ))
    (b : SmallMonomial ι) (d : ι →₀ ℕ) (hd : d ∈ g.support) :
    monomialWeight (smallExponent b + d) ≤ 4 * Fintype.card ι + g.totalDegree := by
  rw [monomialWeight_add]
  exact Nat.add_le_add (smallExponent_weight_le b) (MvPolynomial.le_totalDegree hd)

def polynomialNumeratorLength (g : MvPolynomial ι (Polynomial ℤ)) : ℕ :=
  ∑ d : g.support, coefficientLength (g.coeff d.val)

def productNumerator (R : ι → MvPolynomial ι (Polynomial ℤ))
    (hR : ∀ i d, d ∈ (R i).support → monomialWeight d < 5)
    (D : Polynomial ℤ) (g : MvPolynomial ι (Polynomial ℤ)) (L : ℕ)
    (b : SmallMonomial ι) : SmallMonomial ι → Polynomial ℤ :=
  ∑ d : g.support, fun a => g.coeff d.val *
    D ^ (L - monomialWeight (smallExponent b + d.val)) *
      reduceMonomial R hR D (smallExponent b + d.val) a

theorem productNumerator_evaluation (R : ι → MvPolynomial ι (Polynomial ℤ))
    (hR : ∀ i d, d ∈ (R i).support → monomialWeight d < 5)
    (D : Polynomial ℤ) (g : MvPolynomial ι (Polynomial ℤ)) (L : ℕ)
    (hL : 4 * Fintype.card ι + g.totalDegree ≤ L)
    (f : Polynomial ℤ →+* ℝ) (x : ι → ℝ)
    (hcritical : ∀ i, f D * x i ^ 5 = (R i).eval₂ f x) (b : SmallMonomial ι) :
    numeratorEvaluation f x (productNumerator R hR D g L b) =
      f D ^ L * g.eval₂ f x * smallMonomialValue x b := by
  classical
  unfold productNumerator
  simp only [map_sum, numeratorEvaluation_scale, map_mul, map_pow]
  calc
    (∑ d : g.support,
        f (g.coeff d.val) * f D ^ (L - monomialWeight (smallExponent b + d.val)) *
          numeratorEvaluation f x (reduceMonomial R hR D (smallExponent b + d.val))) =
        ∑ d : g.support, f (g.coeff d.val) * f D ^ L *
          smallMonomialValue x b * monomialValue x d.val := by
      apply Finset.sum_congr rfl
      intro d _
      rw [reduceMonomial_evaluation R hR D f x hcritical,
        monomialValue_add, monomialValue_smallExponent]
      have hd : monomialWeight (smallExponent b + d.val) ≤ L :=
        (productExponent_weight_le g b d.val d.property).trans hL
      have hp : f D ^ (L - monomialWeight (smallExponent b + d.val)) *
          f D ^ monomialWeight (smallExponent b + d.val) = f D ^ L := by
        rw [← pow_add, Nat.sub_add_cancel hd]
      calc
        _ = f (g.coeff d.val) *
            (f D ^ (L - monomialWeight (smallExponent b + d.val)) *
              f D ^ monomialWeight (smallExponent b + d.val)) *
                smallMonomialValue x b * monomialValue x d.val := by ring
        _ = _ := by rw [hp]
    _ = f D ^ L * g.eval₂ f x * smallMonomialValue x b := by
      rw [eval₂_as_small_support, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _
      ring

theorem productNumerator_length (R : ι → MvPolynomial ι (Polynomial ℤ))
    (hR : ∀ i d, d ∈ (R i).support → monomialWeight d < 5)
    (D : Polynomial ℤ) (g : MvPolynomial ι (Polynomial ℤ)) (L C : ℕ)
    (hL : 4 * Fintype.card ι + g.totalDegree ≤ L) (hD : coefficientLength D ≤ C)
    (hcoeff : ∀ i, polynomialNumeratorLength (R i) ≤ C) (b : SmallMonomial ι) :
    numeratorLength (productNumerator R hR D g L b) ≤ polynomialNumeratorLength g * C ^ L := by
  classical
  unfold productNumerator
  apply (numeratorLength_sum_le _ _).trans
  calc
    (∑ d : g.support,
        numeratorLength (fun a => g.coeff d.val *
          D ^ (L - monomialWeight (smallExponent b + d.val)) *
            reduceMonomial R hR D (smallExponent b + d.val) a)) ≤
        ∑ d : g.support, coefficientLength (g.coeff d.val) * C ^ L := by
      apply Finset.sum_le_sum
      intro d _
      have hd : monomialWeight (smallExponent b + d.val) ≤ L :=
        (productExponent_weight_le g b d.val d.property).trans hL
      have hred := reduceMonomial_length R hR D C hD hcoeff (smallExponent b + d.val)
      have hpow := coefficientLength_pow_le_of_le D C hD
        (L - monomialWeight (smallExponent b + d.val))
      calc
        _ ≤ coefficientLength (g.coeff d.val *
              D ^ (L - monomialWeight (smallExponent b + d.val))) *
                numeratorLength (reduceMonomial R hR D (smallExponent b + d.val)) :=
          numeratorLength_scale _ _
        _ ≤ (coefficientLength (g.coeff d.val) *
              coefficientLength (D ^ (L - monomialWeight (smallExponent b + d.val)))) *
                C ^ monomialWeight (smallExponent b + d.val) :=
          Nat.mul_le_mul (coefficientLength_mul_le _ _) hred
        _ ≤ (coefficientLength (g.coeff d.val) *
              C ^ (L - monomialWeight (smallExponent b + d.val))) *
                C ^ monomialWeight (smallExponent b + d.val) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpow)
        _ = coefficientLength (g.coeff d.val) * C ^ L := by
          rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hd]
    _ = polynomialNumeratorLength g * C ^ L := (Finset.sum_mul _ _ _).symm

def multiplicationMatrix (R : ι → MvPolynomial ι (Polynomial ℤ))
    (hR : ∀ i d, d ∈ (R i).support → monomialWeight d < 5)
    (D : Polynomial ℤ) (g : MvPolynomial ι (Polynomial ℤ)) (L : ℕ) :
    Matrix (SmallMonomial ι) (SmallMonomial ι) (Polynomial ℤ) :=
  fun b a => productNumerator R hR D g L b a

theorem multiplicationMatrix_eigenvector (R : ι → MvPolynomial ι (Polynomial ℤ))
    (hR : ∀ i d, d ∈ (R i).support → monomialWeight d < 5)
    (D : Polynomial ℤ) (g : MvPolynomial ι (Polynomial ℤ)) (L : ℕ)
    (hL : 4 * Fintype.card ι + g.totalDegree ≤ L)
    (f : Polynomial ℤ →+* ℝ) (x : ι → ℝ)
    (hcritical : ∀ i, f D * x i ^ 5 = (R i).eval₂ f x) :
    Matrix.mulVec (fun b a => f (multiplicationMatrix R hR D g L b a))
        (smallMonomialValue x) =
      (f D ^ L * g.eval₂ f x) • smallMonomialValue x := by
  ext b
  exact productNumerator_evaluation R hR D g L hL f x hcritical b

omit [DecidableEq ι] in
theorem smallMonomialValue_ne_zero (x : ι → ℝ) : smallMonomialValue x ≠ 0 := by
  intro h
  have hz := congrFun h (fun _ => 0)
  simp [smallMonomialValue] at hz

theorem multiplicationMatrix_entry_length (R : ι → MvPolynomial ι (Polynomial ℤ))
    (hR : ∀ i d, d ∈ (R i).support → monomialWeight d < 5)
    (D : Polynomial ℤ) (g : MvPolynomial ι (Polynomial ℤ)) (L C : ℕ)
    (hL : 4 * Fintype.card ι + g.totalDegree ≤ L) (hD : coefficientLength D ≤ C)
    (hcoeff : ∀ i, polynomialNumeratorLength (R i) ≤ C) (b a : SmallMonomial ι) :
    coefficientLength (multiplicationMatrix R hR D g L b a) ≤ polynomialNumeratorLength g * C ^ L := by
  have hentry : coefficientLength (productNumerator R hR D g L b a) ≤
      numeratorLength (productNumerator R hR D g L b) :=
    Finset.single_le_sum (f := fun a => coefficientLength (productNumerator R hR D g L b a))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  exact hentry.trans (productNumerator_length R hR D g L C hL hD hcoeff b)

#print axioms multiplicationMatrix_eigenvector
#print axioms multiplicationMatrix_entry_length

end
end DInstabilityComplexity.Separation
