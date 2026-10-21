module
public import proofs.DInstabilityComplexity.EliminationMatrix
public import proofs.DInstabilityComplexity.PolynomialWeight
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

/-! # A nonzero bounded eliminant from the constructed multiplication matrix -/

namespace DInstabilityComplexity.Separation

noncomputable section

namespace NatRingWeight

variable {S : Type*} [CommRing S] (W : NatRingWeight S)

theorem sub_le (a b : S) : W (a - b) ≤ W a + W b := by
  simpa only [sub_eq_add_neg, W.neg_eq] using W.add_le a (-b)

theorem lift_C (a : S) : W.lift (Polynomial.C a) = W a :=
  W.polynomialWeight_monomial 0 a

theorem lift_X : W.lift (Polynomial.X : Polynomial S) = 1 := by
  change W.polynomialWeight Polynomial.X = 1
  simpa only [Polynomial.monomial_one_one_eq_X] using
    (W.polynomialWeight_monomial 1 (1 : S)).trans W.one_eq

end NatRingWeight

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {S : Type*} [CommRing S]

def scaledCharmatrix (A : Matrix n n S) (d : S) : Matrix n n (Polynomial S) :=
  Matrix.scalar n (Polynomial.C d * Polynomial.X) - Polynomial.C.mapMatrix A

def scaledEliminant (A : Matrix n n S) (d : S) : Polynomial S := (scaledCharmatrix A d).det

theorem scaledEliminant_eq_comp (A : Matrix n n S) (d : S) :
    scaledEliminant A d = A.charpoly.comp (Polynomial.C d * Polynomial.X) := by
  change (scaledCharmatrix A d).det =
    (Polynomial.eval₂RingHom Polynomial.C (Polynomial.C d * Polynomial.X)) A.charmatrix.det
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [scaledCharmatrix, Matrix.charmatrix]
  · simp [scaledCharmatrix, Matrix.charmatrix, hij]

theorem scaledEliminant_ne_zero [Nontrivial S] [NoZeroDivisors S]
    (A : Matrix n n S) (d : S) (hd : d ≠ 0) : scaledEliminant A d ≠ 0 := by
  rw [scaledEliminant_eq_comp]
  intro h
  rcases Polynomial.comp_eq_zero_iff.mp h with hp | ⟨_, hconst⟩
  · exact A.charpoly_monic.ne_zero hp
  · have hlin : d = 0 := by
      simpa using congrArg (fun p : Polynomial S => p.coeff 1) hconst
    exact hd hlin

theorem scaledEliminant_weight_le (W : NatRingWeight S) (A : Matrix n n S) (d : S)
    (H J : ℕ) (hA : ∀ i j, W (A i j) ≤ H) (hd : W d ≤ J) :
    W.lift (scaledEliminant A d) ≤ (Fintype.card n).factorial * (J + H) ^ Fintype.card n := by
  apply W.lift.det_le
  intro i j
  have hp : W.lift (Polynomial.C d * Polynomial.X) ≤ J := by
    have h := W.lift.mul_le (Polynomial.C d) Polynomial.X
    rw [W.lift_C, W.lift_X, mul_one] at h
    exact h.trans hd
  have hs : W.lift ((Matrix.scalar n (Polynomial.C d * Polynomial.X)) i j) ≤ J := by
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using hp
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, W.lift.zero_eq]
  have hc : W.lift (Polynomial.C (A i j)) ≤ H := by
    rw [W.lift_C]
    exact hA i j
  exact (W.lift.sub_le _ _).trans (Nat.add_le_add hs hc)

theorem scaledEliminant_eval₂ (A : Matrix n n S) (d : S) (f : S →+* ℝ) (u : ℝ) :
    (scaledEliminant A d).eval₂ f u =
      (Matrix.scalar n (f d * u) - A.map f).det := by
  change (Polynomial.eval₂RingHom f u) ((scaledCharmatrix A d).det) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [scaledCharmatrix]
  · simp [scaledCharmatrix, hij]

theorem scaledEliminant_root_of_eigenvector (A : Matrix n n S) (d : S)
    (f : S →+* ℝ) (u : ℝ) (v : n → ℝ) (hv : v ≠ 0)
    (he : Matrix.mulVec (A.map f) v = (f d * u) • v) :
    (scaledEliminant A d).eval₂ f u = 0 := by
  classical
  rw [scaledEliminant_eval₂]
  have hscalar : Matrix.mulVec (Matrix.scalar n (f d * u)) v = (f d * u) • v := by
    ext i
    exact Matrix.mulVec_diagonal _ _ i
  have hker : Matrix.mulVec (Matrix.scalar n (f d * u) - A.map f) v = 0 := by
    rw [Matrix.sub_mulVec, hscalar, he, sub_self]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    simpa only [ne_eq, funext_iff, Pi.zero_apply, not_forall] using hv
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hker
    (i := i) (by simpa using hi)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem constructedEliminant_root (R : ι → MvPolynomial ι (Polynomial ℤ))
    (hR : ∀ i d, d ∈ (R i).support → monomialWeight d < 5)
    (D : Polynomial ℤ) (g : MvPolynomial ι (Polynomial ℤ)) (L : ℕ)
    (hL : 4 * Fintype.card ι + g.totalDegree ≤ L)
    (f : Polynomial ℤ →+* ℝ) (x : ι → ℝ)
    (hcritical : ∀ i, f D * x i ^ 5 = (R i).eval₂ f x) :
    (scaledEliminant (multiplicationMatrix R hR D g L) (D ^ L)).eval₂ f (g.eval₂ f x) = 0 := by
  apply scaledEliminant_root_of_eigenvector _ _ f _ (smallMonomialValue x)
    (smallMonomialValue_ne_zero x)
  ext b
  simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_pow] using
    congrFun (multiplicationMatrix_eigenvector R hR D g L hL f x hcritical) b

theorem constructedEliminant_weight (R : ι → MvPolynomial ι (Polynomial ℤ))
    (hR : ∀ i d, d ∈ (R i).support → monomialWeight d < 5)
    (D : Polynomial ℤ) (g : MvPolynomial ι (Polynomial ℤ)) (L C : ℕ)
    (hL : 4 * Fintype.card ι + g.totalDegree ≤ L) (hD : coefficientLength D ≤ C)
    (hcoeff : ∀ i, polynomialNumeratorLength (R i) ≤ C) :
    twoVariableWeight (scaledEliminant (multiplicationMatrix R hR D g L) (D ^ L)) ≤
      (5 ^ Fintype.card ι).factorial *
        ((polynomialNumeratorLength g + 1) * C ^ L) ^ (5 ^ Fintype.card ι) := by
  have h := scaledEliminant_weight_le integerPolynomialWeight
    (multiplicationMatrix R hR D g L) (D ^ L)
    (polynomialNumeratorLength g * C ^ L) (C ^ L)
    (multiplicationMatrix_entry_length R hR D g L C hL hD hcoeff)
    (coefficientLength_pow_le_of_le D C hD L)
  have hc : C ^ L + polynomialNumeratorLength g * C ^ L =
      (polynomialNumeratorLength g + 1) * C ^ L := by ring
  simpa only [card_smallMonomial, hc, twoVariableWeight] using h

theorem scaledEliminant_integer_coeff_bound
    (A : Matrix n n (Polynomial ℤ)) (d : Polynomial ℤ) (i j : ℕ) :
    (((scaledEliminant A d).coeff j).coeff i).natAbs ≤ twoVariableWeight (scaledEliminant A d) :=
  (natAbs_coeff_le_length _ _).trans (integerPolynomialWeight.coefficient_le_lift _ _)

#print axioms scaledEliminant_ne_zero
#print axioms constructedEliminant_root
#print axioms constructedEliminant_weight

end
end DInstabilityComplexity.Separation
