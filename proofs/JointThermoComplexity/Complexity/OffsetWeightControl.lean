module
public import proofs.JointThermoComplexity.Complexity.RawTemplateFactor
public import proofs.JointThermoComplexity.Complexity.BinaryConstantAdd

set_option autoImplicit false
@[expose] public section

/-! Exact integer weights used in the boxed offset. The template coefficient
and row degree are static; arbitrary source magnitudes remain binary. -/

namespace JointThermoComplexity.Complexity.OffsetWeightControl

def adjusted (negative : Bool) (t : ℤ) : Bool := Bool.xor negative (decide (t < 0))
def constant (d : ℕ) : ℕ := 2 ^ d
def multiplier (t : ℤ) (d : ℕ) : ℕ := 2 * t.natAbs * 2 ^ d
def weight (negative : Bool) (v : ℕ) (t : ℤ) (d : ℕ) : ℕ :=
  if adjusted negative t then constant d else multiplier t d * v + constant d

theorem weight_formula (negative : Bool) (v : ℕ) (t : ℤ) (d : ℕ) :
    weight negative v t d = RationalBranchCoefficients.rightDenominator
      (RationalFactorWords.coefficient (adjusted negative t) (t.natAbs * v)) * 2 ^ d := by
  cases h : adjusted negative t
  · simp only [weight, RationalFactorWords.right_denominator, h, Bool.false_eq_true, ↓reduceIte,
      multiplier, constant]
    ring
  · simp only [weight, RationalFactorWords.right_denominator, h, ↓reduceIte, constant, Nat.one_mul]

theorem weight_integer (c t : ℤ) (d : ℕ) :
    weight (decide (c < 0)) c.natAbs t d = RationalBranchCoefficients.rightDenominator (c * t) * 2 ^ d := by
  rw [weight_formula, adjusted, SignedProductControl.coefficient_product]

theorem weight_pos (negative : Bool) (v : ℕ) (t : ℤ) (d : ℕ) : 0 < weight negative v t d := by
  have hc : 0 < constant d := Nat.two_pow_pos d
  unfold weight
  split <;> omega

theorem static_bounds (t : ℤ) (d : ℕ) (ht : t.natAbs ≤ 81) (hd : d ≤ 4) :
    constant d ≤ 16 ∧ multiplier t d ≤ 2592 := by
  have hc : constant d ≤ 16 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd
  exact ⟨hc, Nat.mul_le_mul (Nat.mul_le_mul_left 2 ht) hc⟩

theorem bits_weight (negative : Bool) (v : ℕ) (t : ℤ) (d : ℕ) :
    (weight negative v t d).bits.length ≤ v.bits.length + multiplier t d + constant d := by
  unfold weight
  split
  · have h := BinaryIncrementControl.bits_length_le (constant d)
    omega
  · have hp := TemplateFactorScratchBounds.product_bits (multiplier t d) v
    have ha := BinaryConstantAdd.bits_add (multiplier t d * v) (constant d)
    omega

end JointThermoComplexity.Complexity.OffsetWeightControl

#print axioms JointThermoComplexity.Complexity.OffsetWeightControl.weight_integer
#print axioms JointThermoComplexity.Complexity.OffsetWeightControl.static_bounds
#print axioms JointThermoComplexity.Complexity.OffsetWeightControl.bits_weight
