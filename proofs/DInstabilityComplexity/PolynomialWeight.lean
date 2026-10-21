module
public import proofs.DInstabilityComplexity.PolynomialLength
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.Int.Units

@[expose] public section

/-!
# Coefficient weights and a determinant height bound

The natural-valued weights below are built from actual coefficient lengths.
Lifting to a polynomial ring controls both variables of the eliminant. The
determinant bound is proved by its finite permutation expansion.
-/

namespace DInstabilityComplexity.Separation

noncomputable section

structure NatRingWeight (S : Type*) [Ring S] where
  weight : S → ℕ
  zero_eq : weight 0 = 0
  one_eq : weight 1 = 1
  neg_eq : ∀ a, weight (-a) = weight a
  add_le : ∀ a b, weight (a + b) ≤ weight a + weight b
  mul_le : ∀ a b, weight (a * b) ≤ weight a * weight b

instance {S : Type*} [Ring S] : CoeFun (NatRingWeight S) (fun _ => S → ℕ) := ⟨NatRingWeight.weight⟩

namespace NatRingWeight

variable {S : Type*} [CommRing S] (W : NatRingWeight S)

theorem sum_le (s : Finset α) (f : α → S) : W (∑ i ∈ s, f i) ≤ ∑ i ∈ s, W (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [W.zero_eq]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (W.add_le _ _).trans (Nat.add_le_add_left ih _)

theorem prod_le (s : Finset α) (f : α → S) : W (∏ i ∈ s, f i) ≤ ∏ i ∈ s, W (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [W.one_eq]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (W.mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

def polynomialWeight (p : Polynomial S) : ℕ := p.sum fun _ a => W a

theorem polynomialWeight_eq_sum (p : Polynomial S) (s : Finset ℕ) (hs : p.support ⊆ s) :
    W.polynomialWeight p = ∑ i ∈ s, W (p.coeff i) :=
  Polynomial.sum_eq_of_subset (fun (_ : ℕ) (a : S) => W a) (fun _ => W.zero_eq) hs

theorem polynomialWeight_zero : W.polynomialWeight 0 = 0 := by
  simp [polynomialWeight, Polynomial.sum_def]

theorem polynomialWeight_monomial (i : ℕ) (a : S) :
    W.polynomialWeight (Polynomial.monomial i a) = W a := by
  classical
  by_cases ha : a = 0
  · simp [ha, polynomialWeight_zero, W.zero_eq]
  · simp [polynomialWeight, Polynomial.sum_def, Polynomial.support_monomial i ha]

theorem polynomialWeight_one : W.polynomialWeight 1 = 1 := by
  simpa only [Polynomial.monomial_zero_left, Polynomial.C_1] using
    (W.polynomialWeight_monomial 0 (1 : S)).trans W.one_eq

theorem polynomialWeight_neg (p : Polynomial S) : W.polynomialWeight (-p) = W.polynomialWeight p := by
  simp only [polynomialWeight, Polynomial.sum_def, Polynomial.support_neg,
    Polynomial.coeff_neg, W.neg_eq]

theorem polynomialWeight_add_le (p q : Polynomial S) :
    W.polynomialWeight (p + q) ≤ W.polynomialWeight p + W.polynomialWeight q := by
  classical
  let T := p.support ∪ q.support
  calc
    W.polynomialWeight (p + q) = ∑ i ∈ T, W ((p + q).coeff i) :=
      W.polynomialWeight_eq_sum _ _ Polynomial.support_add
    _ ≤ ∑ i ∈ T, (W (p.coeff i) + W (q.coeff i)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Polynomial.coeff_add]
      exact W.add_le _ _
    _ = W.polynomialWeight p + W.polynomialWeight q := by
      rw [Finset.sum_add_distrib,
        ← W.polynomialWeight_eq_sum p T Finset.subset_union_left,
        ← W.polynomialWeight_eq_sum q T Finset.subset_union_right]

theorem polynomialWeight_sum_le (s : Finset α) (f : α → Polynomial S) :
    W.polynomialWeight (∑ i ∈ s, f i) ≤ ∑ i ∈ s, W.polynomialWeight (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialWeight_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (W.polynomialWeight_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem polynomialWeight_mul_le (p q : Polynomial S) :
    W.polynomialWeight (p * q) ≤ W.polynomialWeight p * W.polynomialWeight q := by
  classical
  rw [Polynomial.mul_eq_sum_sum]
  simp only [Polynomial.sum_def]
  calc
    W.polynomialWeight (∑ i ∈ p.support, ∑ j ∈ q.support,
        Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) ≤
        ∑ i ∈ p.support, W.polynomialWeight (∑ j ∈ q.support,
          Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) := W.polynomialWeight_sum_le _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
        W.polynomialWeight (Polynomial.monomial (i + j) (p.coeff i * q.coeff j)) := by
      apply Finset.sum_le_sum
      intro i _
      exact W.polynomialWeight_sum_le _ _
    _ = ∑ i ∈ p.support, ∑ j ∈ q.support, W (p.coeff i * q.coeff j) := by
      simp only [polynomialWeight_monomial]
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, W (p.coeff i) * W (q.coeff j) := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun _ _ => W.mul_le _ _
    _ = W.polynomialWeight p * W.polynomialWeight q := by
      simp only [polynomialWeight, Polynomial.sum_def]
      rw [Finset.sum_mul_sum]

def lift : NatRingWeight (Polynomial S) where
  weight := W.polynomialWeight
  zero_eq := W.polynomialWeight_zero
  one_eq := W.polynomialWeight_one
  neg_eq := W.polynomialWeight_neg
  add_le := W.polynomialWeight_add_le
  mul_le := W.polynomialWeight_mul_le

theorem coefficient_le_lift (p : Polynomial S) (i : ℕ) : W (p.coeff i) ≤ W.lift p := by
  classical
  by_cases hi : i ∈ p.support
  · exact Finset.single_le_sum (f := fun j => W (p.coeff j)) (fun _ _ => Nat.zero_le _) hi
  · rw [Polynomial.notMem_support_iff.mp hi, W.zero_eq]
    exact Nat.zero_le _

theorem intUnit_smul (u : ℤˣ) (a : S) : W (u • a) = W a := by
  rcases Int.isUnit_eq_one_or u.isUnit with hu | hu
  · simp [Units.smul_def, hu]
  · simp [Units.smul_def, hu, W.neg_eq]

theorem det_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n S) (H : ℕ) (hA : ∀ i j, W (A i j) ≤ H) :
    W A.det ≤ (Fintype.card n).factorial * H ^ Fintype.card n := by
  classical
  rw [Matrix.det_apply]
  calc
    W (∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, A (σ i) i) ≤
        ∑ σ : Equiv.Perm n, W (Equiv.Perm.sign σ • ∏ i, A (σ i) i) := W.sum_le _ _
    _ = ∑ σ : Equiv.Perm n, W (∏ i, A (σ i) i) := by simp only [W.intUnit_smul]
    _ ≤ ∑ σ : Equiv.Perm n, ∏ i, W (A (σ i) i) :=
      Finset.sum_le_sum fun _ _ => W.prod_le _ _
    _ ≤ ∑ _σ : Equiv.Perm n, H ^ Fintype.card n := by
      apply Finset.sum_le_sum
      intro σ _
      simpa only [Finset.prod_const, Finset.card_univ] using
        (Finset.prod_le_prod fun i (_ : i ∈ (Finset.univ : Finset n)) => hA (σ i) i)
    _ = _ := by simp [Fintype.card_perm]

end NatRingWeight

theorem coefficientLength_neg (p : Polynomial ℤ) : coefficientLength (-p) = coefficientLength p := by
  simp only [coefficientLength, Polynomial.sum_def, Polynomial.support_neg,
    Polynomial.coeff_neg, Int.natAbs_neg]

def integerPolynomialWeight : NatRingWeight (Polynomial ℤ) where
  weight := coefficientLength
  zero_eq := coefficientLength_zero
  one_eq := coefficientLength_one
  neg_eq := coefficientLength_neg
  add_le := coefficientLength_add_le
  mul_le := coefficientLength_mul_le

/-- Total l1 coefficient length in the parameter and value variables. -/
def twoVariableWeight : NatRingWeight (Polynomial (Polynomial ℤ)) := integerPolynomialWeight.lift

#print axioms NatRingWeight.det_le
#print axioms twoVariableWeight

end
end DInstabilityComplexity.Separation
