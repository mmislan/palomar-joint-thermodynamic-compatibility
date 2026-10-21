module
public import proofs.JointThermoComplexity.Complexity.RationalBranchData
public import proofs.JointThermoComplexity.Complexity.RawOffsetBounds
public import proofs.JointThermoComplexity.UnboxedReduction

set_option autoImplicit false
@[expose] public section

/-! Input-fixed natural rational arrays for the raw polynomial construction.
The unboxed offset is an external species, with fixed rational factor data. -/

namespace JointThermoComplexity.Complexity.RationalPolynomialBranches
open SparseInteger RawChemicalPolynomial RationalBranchCoefficients RawOffsetBounds RationalBranchData
variable {V : Type} [DecidableEq V]

def boxedLeft (p : Poly V) : Data V p.length where
  numerator _ := 1
  denominator := Fin.cases (offset p) (fun i => leftDenominator (coefficientInteger p i))
  numerator_pos _ := by decide
  denominator_pos i := Fin.cases (offset_pos p) (fun j => left_pos _) i
  exponent := Fin.cases (fun _ => 0) (exponents p)

def boxedRight (p : Poly V) : Data V p.length where
  numerator _ := 2
  denominator := Fin.cases (offset p) (fun i => rightDenominator (coefficientInteger p i))
  numerator_pos _ := by decide
  denominator_pos i := Fin.cases (offset_pos p) (fun j => right_pos _) i
  exponent := Fin.cases (fun _ => 0) (exponents p)

def unboxedLeft (p : Poly V) : Data (Option V) p.length where
  numerator _ := 1
  denominator := Fin.cases 1 (fun i => leftDenominator (coefficientInteger p i))
  numerator_pos _ := by decide
  denominator_pos i := Fin.cases (by exact Nat.zero_lt_one) (fun j => left_pos _) i
  exponent := Fin.cases (fun v => match v with | none => 1 | some _ => 0)
    (fun i v => match v with | none => 0 | some v => exponents p i v)

def unboxedRight (p : Poly V) : Data (Option V) p.length where
  numerator _ := 2
  denominator := Fin.cases 1 (fun i => rightDenominator (coefficientInteger p i))
  numerator_pos _ := by decide
  denominator_pos i := Fin.cases (by exact Nat.zero_lt_one) (fun j => right_pos _) i
  exponent := Fin.cases (fun v => match v with | none => 1 | some _ => 0)
    (fun i v => match v with | none => 0 | some v => exponents p i v)

theorem branch_ext {E : Type} {n : ℕ} {b c : Emitted.Branch E n}
    (hc : b.coefficient = c.coefficient) (he : b.exponent = c.exponent) : b = c := by
  cases b
  cases c
  cases hc
  cases he
  rfl

theorem boxedLeft_eq [Fintype V] (p : Poly V) :
    (boxedLeft p).toBranch = Emitted.polynomialLeft
      (Emitted.offsetBound (coefficients p) (exponents p))
      (Emitted.offsetBound_pos _ _) (coefficients p) (exponents p) := by
  apply branch_ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Data.toBranch, boxedLeft, Emitted.polynomialLeft, Emitted.offsetBranch,
        Fin.cases_zero, Nat.cast_one, div_one] using offset_real p
    · simpa only [Data.toBranch, boxedLeft, Emitted.polynomialLeft, Emitted.offsetBranch,
        Fin.cases_succ, Nat.cast_one, div_one, coefficients] using left_real (coefficientInteger p j)
  · rfl

theorem boxedRight_eq [Fintype V] (p : Poly V) :
    (boxedRight p).toBranch = Emitted.polynomialRight
      (Emitted.offsetBound (coefficients p) (exponents p))
      (Emitted.offsetBound_pos _ _) (coefficients p) (exponents p) := by
  apply branch_ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (offset p : ℝ) / 2 = Emitted.offsetBound _ _ / 2
      rw [offset_real]
    · change (rightDenominator (coefficientInteger p j) : ℝ) / 2 =
        (coefficients p j + |coefficients p j| + 1) / 2
      rw [right_real]
      rfl
  · rfl

theorem unboxedLeft_eq (p : Poly V) :
    (unboxedLeft p).toBranch = Emitted.unboxedLeft (coefficients p) (exponents p) := by
  apply branch_ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Data.toBranch, unboxedLeft, Emitted.unboxedLeft, Emitted.variableOffsetBranch,
        Fin.cases_zero, Nat.cast_one, div_one]
    · simpa only [Data.toBranch, unboxedLeft, Emitted.unboxedLeft, Emitted.variableOffsetBranch,
        Fin.cases_succ, Nat.cast_one, div_one, coefficients] using left_real (coefficientInteger p j)
  · rfl

theorem unboxedRight_eq (p : Poly V) :
    (unboxedRight p).toBranch = Emitted.unboxedRight (coefficients p) (exponents p) := by
  apply branch_ext
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Data.toBranch, unboxedRight, Emitted.unboxedRight, Emitted.halfBranch,
        Emitted.variableOffsetBranch, Fin.cases_zero, Nat.cast_one, Nat.cast_ofNat]
    · change (rightDenominator (coefficientInteger p j) : ℝ) / 2 =
        (coefficients p j + |coefficients p j| + 1) / 2
      rw [right_real]
      rfl
  · rfl

end JointThermoComplexity.Complexity.RationalPolynomialBranches

#print axioms JointThermoComplexity.Complexity.RationalPolynomialBranches.boxedLeft
#print axioms JointThermoComplexity.Complexity.RationalPolynomialBranches.unboxedRight
#print axioms JointThermoComplexity.Complexity.RationalPolynomialBranches.boxedLeft_eq
#print axioms JointThermoComplexity.Complexity.RationalPolynomialBranches.boxedRight_eq
#print axioms JointThermoComplexity.Complexity.RationalPolynomialBranches.unboxedLeft_eq
#print axioms JointThermoComplexity.Complexity.RationalPolynomialBranches.unboxedRight_eq
