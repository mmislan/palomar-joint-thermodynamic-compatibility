module
public import proofs.DInstabilityComplexity.GradientBounds

@[expose] public section

/-!
# Degree-decreasing numerator reduction

For equations `D*x_i^5 = R_i(x)` with `deg R_i < 5`, this constructs polynomial
numerators in the finite basis with exponents below five. The recursion is on
total monomial degree. Its evaluation identity and quantitative length bound
are subsequent obligations; mere termination does not prove separation.
-/

namespace DInstabilityComplexity.Separation

open MvPolynomial

noncomputable section

variable {ι : Type*}

abbrev SmallMonomial (ι : Type*) := ι → Fin 5

def monomialWeight (m : ι →₀ ℕ) : ℕ := m.sum fun _ n => n

def smallIndex (m : ι →₀ ℕ) (hm : ∀ i, m i < 5) : SmallMonomial ι :=
  fun i => ⟨m i, hm i⟩

def badIndex (m : ι →₀ ℕ) (hm : ¬ ∀ i, m i < 5) : ι :=
  Classical.choose (show ∃ i, 5 ≤ m i from by simpa only [not_forall, not_lt] using hm)

theorem badIndex_ge (m : ι →₀ ℕ) (hm : ¬ ∀ i, m i < 5) : 5 ≤ m (badIndex m hm) :=
  Classical.choose_spec (show ∃ i, 5 ≤ m i from by simpa only [not_forall, not_lt] using hm)

theorem monomialWeight_add (a b : ι →₀ ℕ) :
    monomialWeight (a + b) = monomialWeight a + monomialWeight b := by
  classical
  simp [monomialWeight, Finsupp.sum_add_index]

theorem monomialWeight_sub_five (m : ι →₀ ℕ) (i : ι) (hi : 5 ≤ m i) :
    monomialWeight (m - Finsupp.single i 5) + 5 = monomialWeight m := by
  classical
  have he : m - Finsupp.single i 5 + Finsupp.single i 5 = m := by
    ext j
    by_cases hj : j = i
    · subst j
      simpa [Finsupp.tsub_apply] using Nat.sub_add_cancel hi
    · simp [hj]
  have h := congrArg monomialWeight he
  rw [monomialWeight_add] at h
  simpa [monomialWeight] using h

theorem substitution_degree_lt (m : ι →₀ ℕ) (i : ι) (hi : 5 ≤ m i)
    (d : ι →₀ ℕ) (hd : monomialWeight d < 5) :
    monomialWeight (m - Finsupp.single i 5 + d) < monomialWeight m := by
  rw [monomialWeight_add]
  have h := monomialWeight_sub_five m i hi
  omega

variable [Fintype ι] [DecidableEq ι]

theorem card_smallMonomial : Fintype.card (SmallMonomial ι) = 5 ^ Fintype.card ι := by
  simp [SmallMonomial]

omit [DecidableEq ι] in
theorem smallMonomial_weight_le (b : SmallMonomial ι) :
    (∑ i, (b i).val) ≤ 4 * Fintype.card ι := by
  calc
    (∑ i, (b i).val) ≤ ∑ _i : ι, 4 :=
      Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (b i).isLt
    _ = 4 * Fintype.card ι := by simp [Nat.mul_comm]

/-- Numerators use the common denominator `D^(monomialWeight m)`. Each
recursive substitution lowers total degree and keeps all coefficients in Z[T]. -/
def reduceMonomial (R : ι → MvPolynomial ι (Polynomial ℤ))
    (hR : ∀ i d, d ∈ (R i).support → monomialWeight d < 5)
    (D : Polynomial ℤ) (m : ι →₀ ℕ) : SmallMonomial ι → Polynomial ℤ := by
  classical
  exact if hm : ∀ i, m i < 5 then
    fun b => if b = smallIndex m hm then D ^ monomialWeight m else 0
  else
    let i := badIndex m hm
    ∑ d : (R i).support, fun b =>
      (R i).coeff d.val *
        D ^ (monomialWeight m - 1 - monomialWeight (m - Finsupp.single i 5 + d.val)) *
        reduceMonomial R hR D (m - Finsupp.single i 5 + d.val) b
termination_by monomialWeight m
decreasing_by
  exact substitution_degree_lt m (badIndex m hm) (badIndex_ge m hm) d.val (hR _ _ d.property)

theorem card_torus_smallMonomial (k : ℕ) :
    Fintype.card (SmallMonomial (TorusCoords k)) = 5 ^ (2 * k) := by
  simp [SmallMonomial, TorusCoords, Nat.mul_comm]

#print axioms substitution_degree_lt
#print axioms reduceMonomial

end
end DInstabilityComplexity.Separation
