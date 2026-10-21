module
public import proofs.DInstabilityComplexity.SeparationRoot

@[expose] public section

/-!
# Integer-polynomial coefficient length

These bounds will control numerators in degree-reducing substitutions and in
the determinant expansion of the elimination matrix. Length is the sum of the
absolute integer coefficients, so every individual coefficient is bounded by it.
-/

namespace DInstabilityComplexity.Separation

open Polynomial

noncomputable section

def coefficientLength (p : ℤ[X]) : ℕ := p.sum fun _ z => z.natAbs

@[simp] theorem coefficientLength_zero : coefficientLength (0 : ℤ[X]) = 0 := by
  simp [coefficientLength, Polynomial.sum_def]

theorem natAbs_coeff_le_length (p : ℤ[X]) (i : ℕ) :
    (p.coeff i).natAbs ≤ coefficientLength p := by
  classical
  by_cases hi : i ∈ p.support
  · change (p.coeff i).natAbs ≤ ∑ j ∈ p.support, (p.coeff j).natAbs
    exact Finset.single_le_sum (f := fun j => (p.coeff j).natAbs) (fun _ _ => Nat.zero_le _) hi
  · simp [Polynomial.notMem_support_iff.mp hi]

theorem coefficientLength_eq_sum_of_support_subset (p : ℤ[X]) (s : Finset ℕ)
    (hs : p.support ⊆ s) : coefficientLength p = ∑ i ∈ s, (p.coeff i).natAbs :=
  Polynomial.sum_eq_of_subset (fun (_ : ℕ) (z : ℤ) => z.natAbs) (fun _ => rfl) hs

@[simp] theorem coefficientLength_monomial (i : ℕ) (z : ℤ) :
    coefficientLength (Polynomial.monomial i z) = z.natAbs := by
  classical
  by_cases hz : z = 0
  · simp [hz]
  · simp [coefficientLength, Polynomial.sum_def, Polynomial.support_monomial i hz]

@[simp] theorem coefficientLength_one : coefficientLength (1 : ℤ[X]) = 1 := by
  simpa only [Polynomial.monomial_zero_left, Polynomial.C_1,
    show (1 : ℤ).natAbs = 1 by decide] using
    coefficientLength_monomial 0 (1 : ℤ)

theorem coefficientLength_add_le (p q : ℤ[X]) :
    coefficientLength (p + q) ≤ coefficientLength p + coefficientLength q := by
  classical
  let S := p.support ∪ q.support
  have hp : p.support ⊆ S := Finset.subset_union_left
  have hq : q.support ⊆ S := Finset.subset_union_right
  calc
    coefficientLength (p + q) = ∑ i ∈ S, ((p + q).coeff i).natAbs :=
      coefficientLength_eq_sum_of_support_subset _ _ Polynomial.support_add
    _ ≤ ∑ i ∈ S, ((p.coeff i).natAbs + (q.coeff i).natAbs) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Polynomial.coeff_add]
      exact Int.natAbs_add_le _ _
    _ = coefficientLength p + coefficientLength q := by
      rw [Finset.sum_add_distrib,
        ← coefficientLength_eq_sum_of_support_subset p S hp,
        ← coefficientLength_eq_sum_of_support_subset q S hq]

theorem coefficientLength_sum_le (s : Finset ι) (f : ι → ℤ[X]) :
    coefficientLength (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coefficientLength (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (coefficientLength_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem coefficientLength_mul_le (p q : ℤ[X]) :
    coefficientLength (p * q) ≤ coefficientLength p * coefficientLength q := by
  classical
  rw [Polynomial.mul_eq_sum_sum]
  simp only [Polynomial.sum_def]
  calc
    coefficientLength (∑ i ∈ p.support, ∑ j ∈ q.support,
        Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) ≤
        ∑ i ∈ p.support, coefficientLength (∑ j ∈ q.support,
          Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) := coefficientLength_sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
        coefficientLength (Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) := by
      apply Finset.sum_le_sum
      intro i _
      exact coefficientLength_sum_le _ _
    _ = coefficientLength p * coefficientLength q := by
      simp only [coefficientLength_monomial, Int.natAbs_mul]
      simp only [coefficientLength, Polynomial.sum_def]
      rw [Finset.sum_mul_sum]

theorem coefficientLength_pow_le (p : ℤ[X]) (n : ℕ) :
    coefficientLength (p ^ n) ≤ coefficientLength p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (coefficientLength_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

#print axioms coefficientLength_mul_le
#print axioms coefficientLength_pow_le

end
end DInstabilityComplexity.Separation
