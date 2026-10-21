module
public import proofs.JointThermoComplexity.Complexity.DenseProductEmit
public import proofs.JointThermoComplexity.Complexity.ReactionBuildCode

set_option autoImplicit false
@[expose] public section

/-! Exact original factor fields and the existing reaction-record codec. -/

namespace JointThermoComplexity.Complexity.DenseFactorCode
open RationalBranchData RationalPolynomialBranches
variable {e N : ℕ} {E : Type}

def factor (right : Bool) (L Rdata : Data (Fin e) N) (i : Fin (N + 2)) : List Bool :=
  BitCodec.naturalCode (RationalLiteralNetwork.reaction L Rdata (DenseComplexOriginal.index right N i)).numerator ++
    BitCodec.naturalCode (RationalLiteralNetwork.reaction L Rdata (DenseComplexOriginal.index right N i)).denominator

theorem factor_left (L Rdata : Data (Fin e) N) (i : Fin (N + 2)) :
    factor false L Rdata i = BitCodec.naturalCode (L.numeratorAt i) ++ BitCodec.naturalCode (L.denominatorAt i) := by
  simp only [factor, DenseComplexOriginal.index, Bool.false_eq_true, ↓reduceIte,
    RationalLiteralNetwork.reaction, Equiv.symm_apply_apply, RationalLiteralNetwork.numeratorRaw,
    RationalLiteralNetwork.denominatorRaw, Sum.elim_inl]

theorem factor_right (L Rdata : Data (Fin e) N) (i : Fin (N + 2)) :
    factor true L Rdata i = BitCodec.naturalCode (Rdata.numeratorAt i) ++ BitCodec.naturalCode (Rdata.denominatorAt i) := by
  simp only [factor, DenseComplexOriginal.index, ↓reduceIte,
    RationalLiteralNetwork.reaction, Equiv.symm_apply_apply, RationalLiteralNetwork.numeratorRaw,
    RationalLiteralNetwork.denominatorRaw, Sum.elim_inr]

theorem numerator_zero (b : Data E N) : b.numeratorAt 0 = 1 := by
  simp only [Data.numeratorAt, Fin.val_zero, ↓reduceDIte]
theorem denominator_zero (b : Data E N) : b.denominatorAt 0 = 1 := by
  simp only [Data.denominatorAt, Fin.val_zero, ↓reduceDIte]

theorem numerator_succ (b : Data E N) (i : Fin (N + 1)) : b.numeratorAt i.succ = b.numerator i := by
  unfold Data.numeratorAt
  rw [dite_eq_right (by change i.val + 1 ≠ 0; omega)]
  congr 1
theorem denominator_succ (b : Data E N) (i : Fin (N + 1)) : b.denominatorAt i.succ = b.denominator i := by
  unfold Data.denominatorAt
  rw [dite_eq_right (by change i.val + 1 ≠ 0; omega)]
  congr 1

theorem factor_zero (right : Bool) (L Rdata : Data (Fin e) N) :
    factor right L Rdata 0 = BitCodec.naturalCode 1 ++ BitCodec.naturalCode 1 := by
  cases right
  · rw [factor_left, numerator_zero, denominator_zero]
  · rw [factor_right, numerator_zero, denominator_zero]

theorem regular_code (boxed right : Bool) (p : SparsePolynomialCodec.PolynomialData) (j : Fin p.payload.length) :
    factor right (RationalPolynomialNetwork.left boxed p) (RationalPolynomialNetwork.right boxed p) j.succ.succ =
      RationalFactorWords.word right (RawChemicalPolynomial.coefficientInteger p.payload j) := by
  cases right with
  | false =>
    rw [factor_left, numerator_succ, denominator_succ]
    cases boxed
    · simp only [RationalPolynomialNetwork.left, RationalBranchRelabel.relabel, unboxedLeft, Fin.cases_succ,
        RationalFactorWords.word, Bool.false_eq_true, ↓reduceIte]
    · simp only [RationalPolynomialNetwork.left, boxedLeft, Fin.cases_succ,
        RationalFactorWords.word, Bool.false_eq_true, ↓reduceIte]
  | true =>
    rw [factor_right, numerator_succ, denominator_succ]
    cases boxed
    · simp only [RationalPolynomialNetwork.right, RationalBranchRelabel.relabel, unboxedRight, Fin.cases_succ,
        RationalFactorWords.word, ↓reduceIte]
    · simp only [RationalPolynomialNetwork.right, boxedRight, Fin.cases_succ, RationalFactorWords.word, ↓reduceIte]

def fixedWord (boxed right offset : Bool) (U : ℕ) : List Bool :=
  if offset then BitCodec.naturalCode (if right then 2 else 1) ++ BitCodec.naturalCode (if boxed then U else 1)
  else BitCodec.naturalCode 1 ++ BitCodec.naturalCode 1

theorem fixed_code (boxed right offset : Bool) (p : SparsePolynomialCodec.PolynomialData) :
    factor right (RationalPolynomialNetwork.left boxed p) (RationalPolynomialNetwork.right boxed p)
      (DenseFixedComplexOriginal.initialVertex offset p.payload.length) = fixedWord boxed right offset (RawOffsetBounds.offset p.payload) := by
  cases offset with
  | false =>
    simp only [fixedWord, DenseFixedComplexOriginal.initialVertex, Bool.false_eq_true, ↓reduceIte, factor_zero]
  | true =>
    simp only [fixedWord, DenseFixedComplexOriginal.initialVertex, ↓reduceIte]
    cases right with
    | false =>
      rw [factor_left, numerator_succ, denominator_succ]
      cases boxed
      · simp only [RationalPolynomialNetwork.left, RationalBranchRelabel.relabel, unboxedLeft, Fin.cases_zero,
          Bool.false_eq_true, ↓reduceIte]
      · simp only [RationalPolynomialNetwork.left, boxedLeft, Fin.cases_zero, Bool.false_eq_true, ↓reduceIte]
    | true =>
      rw [factor_right, numerator_succ, denominator_succ]
      cases boxed
      · simp only [RationalPolynomialNetwork.right, RationalBranchRelabel.relabel, unboxedRight, Fin.cases_zero,
          Bool.false_eq_true, ↓reduceIte]
      · simp only [RationalPolynomialNetwork.right, boxedRight, Fin.cases_zero, ↓reduceIte]

theorem record_code (right : Bool) (L Rdata : Data (Fin e) N) (i : Fin (N + 2)) :
    (DataCodec.reaction (RationalLiteralNetwork.speciesCount e N N)).code
      (RationalLiteralNetwork.reaction L Rdata (DenseComplexOriginal.index right N i)) =
      (FiniteCodec.functionCode FiniteCodec.natural (DenseComplexOriginal.complex right false L Rdata i) ++
        FiniteCodec.functionCode FiniteCodec.natural (DenseComplexOriginal.complex right true L Rdata i)) ++ factor right L Rdata i :=
  ReactionBuildCode.record_code _

end JointThermoComplexity.Complexity.DenseFactorCode

#print axioms JointThermoComplexity.Complexity.DenseFactorCode.regular_code
#print axioms JointThermoComplexity.Complexity.DenseFactorCode.fixed_code
#print axioms JointThermoComplexity.Complexity.DenseFactorCode.record_code
