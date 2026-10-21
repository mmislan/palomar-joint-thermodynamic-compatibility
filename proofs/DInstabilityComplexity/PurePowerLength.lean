module
public import proofs.DInstabilityComplexity.PurePowerReduction

@[expose] public section

/-! # Quantitative growth of the constructed reduction numerators -/

namespace DInstabilityComplexity.Separation

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def numeratorLength (v : SmallMonomial ι → Polynomial ℤ) : ℕ :=
  ∑ b, coefficientLength (v b)

theorem numeratorLength_scale (c : Polynomial ℤ) (v : SmallMonomial ι → Polynomial ℤ) :
    numeratorLength (fun b => c * v b) ≤ coefficientLength c * numeratorLength v := by
  unfold numeratorLength
  calc
    (∑ b, coefficientLength (c * v b)) ≤ ∑ b, coefficientLength c * coefficientLength (v b) :=
      Finset.sum_le_sum fun _ _ => coefficientLength_mul_le _ _
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem numeratorLength_sum_le (s : Finset α) (v : α → SmallMonomial ι → Polynomial ℤ) :
    numeratorLength (∑ a ∈ s, v a) ≤ ∑ a ∈ s, numeratorLength (v a) := by
  classical
  simp only [numeratorLength, Finset.sum_apply]
  calc
    (∑ b, coefficientLength (∑ a ∈ s, v a b)) ≤
        ∑ b, ∑ a ∈ s, coefficientLength (v a b) :=
      Finset.sum_le_sum fun b _ => coefficientLength_sum_le _ _
    _ = _ := Finset.sum_comm

theorem numeratorLength_delta (b₀ : SmallMonomial ι) (p : Polynomial ℤ) :
    numeratorLength (fun b => if b = b₀ then p else 0) = coefficientLength p := by
  classical
  simp [numeratorLength, apply_ite]

theorem coefficientLength_pow_le_of_le (p : Polynomial ℤ) (C : ℕ)
    (hC : coefficientLength p ≤ C) (n : ℕ) : coefficientLength (p ^ n) ≤ C ^ n :=
  (coefficientLength_pow_le p n).trans (Nat.pow_le_pow_left hC n)

/-- The length of the actual constructed numerator vector grows at most
exponentially in the input monomial degree. These are local coefficient bounds
on the given equations, not a hypothesis about their solutions or minima. -/
theorem reduceMonomial_length (R : ι → MvPolynomial ι (Polynomial ℤ))
    (hR : ∀ i d, d ∈ (R i).support → monomialWeight d < 5)
    (D : Polynomial ℤ) (C : ℕ) (hD : coefficientLength D ≤ C)
    (hcoeff : ∀ i, (∑ d : (R i).support, coefficientLength ((R i).coeff d.val)) ≤ C)
    (m : ι →₀ ℕ) :
    numeratorLength (reduceMonomial R hR D m) ≤ C ^ monomialWeight m := by
  classical
  induction m using (measure monomialWeight).wf.induction with
  | h m ih =>
    by_cases hm : ∀ i, m i < 5
    · rw [reduceMonomial, dite_eq_left hm, numeratorLength_delta]
      exact coefficientLength_pow_le_of_le D C hD _
    · let i := badIndex m hm
      let q := m - Finsupp.single i 5
      have hi : 5 ≤ m i := badIndex_ge m hm
      have hweight := monomialWeight_sub_five m i hi
      have hN : 0 < monomialWeight m := by omega
      have hstep : numeratorLength (reduceMonomial R hR D m) ≤
          ∑ d : (R i).support,
            numeratorLength (fun b => (R i).coeff d.val *
              D ^ (monomialWeight m - 1 - monomialWeight (q + d.val)) *
                reduceMonomial R hR D (q + d.val) b) := by
        rw [reduceMonomial, dite_eq_right hm]
        exact numeratorLength_sum_le _ _
      apply hstep.trans
      calc
        (∑ d : (R i).support,
            numeratorLength (fun b => (R i).coeff d.val *
              D ^ (monomialWeight m - 1 - monomialWeight (q + d.val)) *
                reduceMonomial R hR D (q + d.val) b)) ≤
            ∑ d : (R i).support, coefficientLength ((R i).coeff d.val) *
              C ^ (monomialWeight m - 1) := by
          apply Finset.sum_le_sum
          intro d _
          have hd : monomialWeight (q + d.val) < monomialWeight m :=
            substitution_degree_lt m i hi d.val (hR i d.val d.property)
          have hind := ih (q + d.val) hd
          have hpow := coefficientLength_pow_le_of_le D C hD
            (monomialWeight m - 1 - monomialWeight (q + d.val))
          calc
            _ ≤ coefficientLength ((R i).coeff d.val *
                  D ^ (monomialWeight m - 1 - monomialWeight (q + d.val))) *
                    numeratorLength (reduceMonomial R hR D (q + d.val)) := numeratorLength_scale _ _
            _ ≤ (coefficientLength ((R i).coeff d.val) *
                  coefficientLength (D ^ (monomialWeight m - 1 - monomialWeight (q + d.val)))) *
                    C ^ monomialWeight (q + d.val) :=
              Nat.mul_le_mul (coefficientLength_mul_le _ _) hind
            _ ≤ (coefficientLength ((R i).coeff d.val) *
                  C ^ (monomialWeight m - 1 - monomialWeight (q + d.val))) *
                    C ^ monomialWeight (q + d.val) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpow)
            _ = coefficientLength ((R i).coeff d.val) * C ^ (monomialWeight m - 1) := by
              rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
        _ = (∑ d : (R i).support, coefficientLength ((R i).coeff d.val)) *
            C ^ (monomialWeight m - 1) := (Finset.sum_mul _ _ _).symm
        _ ≤ C * C ^ (monomialWeight m - 1) := Nat.mul_le_mul_right _ (hcoeff i)
        _ = C ^ monomialWeight m := by
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hN]

#print axioms reduceMonomial_length

end
end DInstabilityComplexity.Separation
