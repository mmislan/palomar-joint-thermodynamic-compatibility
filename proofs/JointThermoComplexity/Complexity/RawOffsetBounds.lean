module
public import proofs.JointThermoComplexity.Complexity.RawChemicalPolynomial
public import proofs.JointThermoComplexity.Complexity.RationalBranchCoefficients
public import proofs.JointThermoComplexity.BoxedSource

set_option autoImplicit false
@[expose] public section

/-! The boxed offset is a positive input-fixed integer with a linear bound
at fixed degree and coefficient magnitude. -/

namespace JointThermoComplexity.Complexity.RawOffsetBounds
open SparseInteger RawChemicalPolynomial RationalBranchCoefficients
open scoped BigOperators
variable {V : Type}

def offset (p : Poly V) : ℕ :=
  1 + ∑ i : Fin p.length, rightDenominator (coefficientInteger p i) * 2 ^ p[i].2.length

theorem offset_pos (p : Poly V) : 0 < offset p := by unfold offset; omega

theorem power_product [Fintype V] [DecidableEq V] (p : Poly V) (i : Fin p.length) :
    (∏ v, (2 : ℝ) ^ exponents p i v) = 2 ^ p[i].2.length := by
  unfold exponents
  have h (vs : List V) : (vs.map (fun _ => (2 : ℝ))).prod = (2 : ℝ) ^ vs.length := by
    induction vs with
    | nil => simp
    | cons v vs ih => simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ', ih]
  rw [← product_counts]
  exact h _

theorem offset_real [Fintype V] [DecidableEq V] (p : Poly V) :
    (offset p : ℝ) = Emitted.offsetBound (coefficients p) (exponents p) := by
  simp only [offset, Nat.cast_add, Nat.cast_one, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold Emitted.offsetBound
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [power_product, right_real]
  rfl

theorem offset_bound {C d : ℕ} (p : Poly V) (hp : DegreeLE d p) (hc : CoefficientsLE C p) :
    offset p ≤ 1 + p.length * ((2 * C + 1) * 2 ^ d) := by
  have hs : (∑ i : Fin p.length, rightDenominator (coefficientInteger p i) * 2 ^ p[i].2.length) ≤
      p.length * ((2 * C + 1) * 2 ^ d) := by
    calc
      _ ≤ ∑ _i : Fin p.length, (2 * C + 1) * 2 ^ d := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.mul_le_mul (right_bound _ (coefficient_bound p hc i))
          (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (hp _ (List.getElem_mem i.isLt)))
      _ = _ := by simp
  exact Nat.add_le_add_left hs 1

theorem coefficient_denominator_bits (c : ℤ) (hc : c.natAbs ≤ 530841600) :
    leftDenominator c < (2 : ℕ) ^ 30 ∧ rightDenominator c < (2 : ℕ) ^ 30 :=
  ⟨(left_bound c hc).trans_lt (by decide), (right_bound c hc).trans_lt (by decide)⟩

end JointThermoComplexity.Complexity.RawOffsetBounds

#print axioms JointThermoComplexity.Complexity.RawOffsetBounds.offset
#print axioms JointThermoComplexity.Complexity.RawOffsetBounds.offset_real
#print axioms JointThermoComplexity.Complexity.RawOffsetBounds.offset_bound
