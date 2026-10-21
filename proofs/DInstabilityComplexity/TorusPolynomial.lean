module
public import proofs.DInstabilityComplexity.SeparationRoot
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

@[expose] public section

/-!
# The quadratic polynomial entering torus separation

The two real coordinates for each complex variable are represented explicitly.
The coefficient bound uses the fact that a quadratic monomial has at most two
ordered factorizations into variables; it does not multiply the height by the
number of columns. No effective elimination theorem is postulated here.
-/

namespace DInstabilityComplexity.Separation

open MvPolynomial

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pairKey (i j : ι) : ι →₀ ℕ := Finsupp.single i 1 + Finsupp.single j 1

omit [Fintype ι] in
theorem pairKey_eq_iff (a b c d : ι) :
    pairKey a b = pairKey c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a = c ∨ a = d := by
      by_contra hn
      push Not at hn
      have he := congrArg (fun f : ι →₀ ℕ => f a) h
      simp [pairKey, Finsupp.single_apply, hn.1, hn.2] at he
    rcases ha with hac | had
    · have he := h
      unfold pairKey at he
      rw [← hac] at he
      have hb := Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)
        (add_left_cancel he)
      exact Or.inl ⟨hac, hb⟩
    · have he := h
      unfold pairKey at he
      rw [← had] at he
      have he' : Finsupp.single a 1 + Finsupp.single b 1 =
          Finsupp.single a 1 + Finsupp.single c 1 := he.trans (add_comm _ _)
      have hb := Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)
        (add_left_cancel he')
      exact Or.inr ⟨had, hb⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [pairKey, add_comm]

theorem card_pairKey_fiber_le_two (d : ι →₀ ℕ) :
    (Finset.univ.filter fun p : ι × ι => pairKey p.1 p.2 = d).card ≤ 2 := by
  classical
  let S := Finset.univ.filter fun p : ι × ι => pairKey p.1 p.2 = d
  change S.card ≤ 2
  rcases S.eq_empty_or_nonempty with hs | ⟨p, hp⟩
  · simp [hs]
  · have hpkey : pairKey p.1 p.2 = d := (Finset.mem_filter.mp hp).2
    have hsub : S ⊆ {p, (p.2, p.1)} := by
      intro q hq
      have hqkey : pairKey q.1 q.2 = d := (Finset.mem_filter.mp hq).2
      rcases (pairKey_eq_iff q.1 q.2 p.1 p.2).mp (hqkey.trans hpkey.symm) with h | h
      · have he : q = p := Prod.ext h.1 h.2
        simp [he]
      · have he : q = (p.2, p.1) := Prod.ext h.1 h.2
        simp [he]
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))

def quadraticPolynomial (G : Matrix ι ι ℤ) : MvPolynomial ι ℤ :=
  ∑ p : ι × ι, monomial (pairKey p.1 p.2) (G p.1 p.2)

theorem quadraticPolynomial_coeff_le (G : Matrix ι ι ℤ) (H : ℤ) (hH : 0 ≤ H)
    (hG : ∀ i j, |G i j| ≤ H) (d : ι →₀ ℕ) :
    |(quadraticPolynomial G).coeff d| ≤ 2 * H := by
  classical
  let S := Finset.univ.filter fun p : ι × ι => pairKey p.1 p.2 = d
  have he : (quadraticPolynomial G).coeff d = ∑ p ∈ S, G p.1 p.2 := by
    simp [quadraticPolynomial, S, Finset.sum_filter]
  rw [he]
  calc
    |∑ p ∈ S, G p.1 p.2| ≤ ∑ p ∈ S, |G p.1 p.2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ S, H := Finset.sum_le_sum fun p _ => hG p.1 p.2
    _ = (S.card : ℤ) * H := by simp
    _ ≤ 2 * H := mul_le_mul_of_nonneg_right (by exact_mod_cast card_pairKey_fiber_le_two d) hH

theorem quadraticPolynomial_totalDegree_le (G : Matrix ι ι ℤ) :
    (quadraticPolynomial G).totalDegree ≤ 2 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro p _
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  simp [pairKey, Finsupp.sum_add_index]

omit [DecidableEq ι] in
theorem eval_quadraticPolynomial (G : Matrix ι ι ℤ) (x : ι → ℝ) :
    (quadraticPolynomial G).eval₂ (Int.castRingHom ℝ) x =
      ∑ i, ∑ j, (G i j : ℝ) * x i * x j := by
  classical
  simp only [quadraticPolynomial, MvPolynomial.eval₂_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pairKey, MvPolynomial.monomial_add_single, pow_one,
    ← MvPolynomial.C_mul_X_eq_monomial]
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C]
  rfl

/-- Real and imaginary coordinates of each torus variable. -/
abbrev TorusCoords (k : ℕ) := Fin k × Bool

def torusGram (M : Matrix (Fin r) (Fin k) ℤ) :
    Matrix (TorusCoords k) (TorusCoords k) ℤ :=
  fun u v => if u.2 = v.2 then ∑ c, M c u.1 * M c v.1 else 0

def torusPolynomial (M : Matrix (Fin r) (Fin k) ℤ) : MvPolynomial (TorusCoords k) ℤ :=
  quadraticPolynomial (torusGram M)

theorem torusGram_abs_le (M : Matrix (Fin r) (Fin k) ℤ) (B : ℕ)
    (hM : ∀ c e, |M c e| ≤ (B : ℤ)) (u v : TorusCoords k) :
    |torusGram M u v| ≤ (r : ℤ) * (B : ℤ) ^ 2 := by
  classical
  unfold torusGram
  split_ifs
  · calc
      |∑ c, M c u.1 * M c v.1| ≤ ∑ c, |M c u.1 * M c v.1| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _c : Fin r, (B : ℤ) ^ 2 := by
        apply Finset.sum_le_sum
        intro c _
        rw [abs_mul, pow_two]
        exact mul_le_mul (hM c u.1) (hM c v.1) (abs_nonneg _) (by positivity)
      _ = (r : ℤ) * (B : ℤ) ^ 2 := by simp
  · simp only [abs_zero]
    positivity

/-- The exact coefficient height used by the JPT specialization. -/
theorem torusPolynomial_coeff_bound (M : Matrix (Fin r) (Fin k) ℤ) (B : ℕ)
    (hM : ∀ c e, |M c e| ≤ (B : ℤ)) (d : TorusCoords k →₀ ℕ) :
    |(torusPolynomial M).coeff d| ≤ ((2 * r * B ^ 2 : ℕ) : ℤ) := by
  have h := quadraticPolynomial_coeff_le (torusGram M) ((r : ℤ) * (B : ℤ) ^ 2)
    (by positivity) (torusGram_abs_le M B hM) d
  simpa only [torusPolynomial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_assoc] using h

theorem torusPolynomial_totalDegree_le (M : Matrix (Fin r) (Fin k) ℤ) :
    (torusPolynomial M).totalDegree ≤ 2 := quadraticPolynomial_totalDegree_le _

theorem gram_eval_square (M : Matrix (Fin r) (Fin k) ℤ) (x : Fin k → ℝ) :
    (∑ i, ∑ j, (∑ c, (M c i : ℝ) * (M c j : ℝ)) * x i * x j) =
      ∑ c, (∑ i, (M c i : ℝ) * x i) ^ 2 := by
  simp only [Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ c, (M c i : ℝ) * M c j * x i * x j) =
        ∑ i, ∑ c, ∑ j, ((M c i : ℝ) * x i) * ((M c j : ℝ) * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ c, ∑ i, ∑ j, ((M c i : ℝ) * x i) * ((M c j : ℝ) * x j) := Finset.sum_comm
    _ = ∑ c, (∑ i, (M c i : ℝ) * x i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [pow_two, Fintype.sum_mul_sum]

theorem eval_torusPolynomial (M : Matrix (Fin r) (Fin k) ℤ) (x : TorusCoords k → ℝ) :
    (torusPolynomial M).eval₂ (Int.castRingHom ℝ) x =
      ∑ c, ((∑ e, (M c e : ℝ) * x (e, false)) ^ 2 +
        (∑ e, (M c e : ℝ) * x (e, true)) ^ 2) := by
  rw [torusPolynomial, eval_quadraticPolynomial]
  simp [Fintype.sum_prod_type, torusGram, Finset.sum_add_distrib]
  rw [gram_eval_square M (fun e => x (e, true)), gram_eval_square M (fun e => x (e, false))]
  ring

#print axioms torusPolynomial_coeff_bound
#print axioms torusPolynomial_totalDegree_le
#print axioms eval_torusPolynomial

end
end DInstabilityComplexity.Separation
