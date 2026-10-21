module
public import proofs.JointThermoComplexity.Complexity.RowWordCodec
public import proofs.JointThermoComplexity.Complexity.PreorderFormulaEmission

set_option autoImplicit false
@[expose] public section

/-! The total equation control has an exact marked-row serialization specification. -/

namespace JointThermoComplexity.Complexity.PreorderRowCode
open SparseInteger

def numericTerm (a : ℤ × List ℕ) : List Bool :=
  BitCodec.integerCode a.1 ++ RowWordCodec.marked BitCodec.naturalCode a.2

def numericPolynomial (p : Poly ℕ) : List Bool := RowWordCodec.marked numericTerm p

def numericRows (ps : List (Poly ℕ)) : List Bool := RowWordCodec.marked numericPolynomial ps

theorem term_words (a : ℤ × List ℕ) :
    RowWordCodec.term (a.1, a.2.map BitCodec.naturalCode) = numericTerm a := by
  rw [RowWordCodec.term, RowWordCodec.monomial, RowWordCodec.marked_map]
  rfl

theorem polynomial_words (p : Poly ℕ) :
    RowWordCodec.polynomial (relabel BitCodec.naturalCode p) = numericPolynomial p := by
  induction p with
  | nil => rfl
  | cons a rest ih =>
    change true :: (RowWordCodec.term (a.1, a.2.map BitCodec.naturalCode) ++
      RowWordCodec.polynomial (relabel BitCodec.naturalCode rest)) =
        true :: (numericTerm a ++ numericPolynomial rest)
    rw [term_words, ih]

theorem rows_words (ps : List (Poly ℕ)) :
    RowWordCodec.rows (PreorderLocalRows.words ps) = numericRows ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    change true :: (RowWordCodec.polynomial (relabel BitCodec.naturalCode p) ++
      RowWordCodec.rows (PreorderLocalRows.words rest)) = true :: (numericPolynomial p ++ numericRows rest)
    rw [polynomial_words, ih]

def code (input : List Bool) : List Bool := RowWordCodec.rows (PreorderFormulaEmission.rows input)

def normalized (input : List Bool) : List Bool := code (SmallSyntaxFP.code input)

theorem normalized_eq (input : List Bool) : normalized input = numericRows (PreorderSourceEquations.normalized input) := by
  change RowWordCodec.rows (PreorderFormulaEmission.normalized input) = _
  rw [PreorderFormulaEmission.normalized_eq, rows_words]

theorem numericPolynomial_finite (n : ℕ) (p : Poly (Fin n)) :
    numericPolynomial (relabel Fin.val p) = (SparsePolynomialCodec.polynomial n).code p := by
  induction p with
  | nil => rfl
  | cons a rest ih =>
    change true :: (numericTerm (a.1, a.2.map Fin.val) ++ numericPolynomial (relabel Fin.val rest)) =
      true :: ((SparsePolynomialCodec.term n).code a ++ (SparsePolynomialCodec.polynomial n).code rest)
    rw [ih]
    congr 2
    change BitCodec.integerCode a.1 ++ RowWordCodec.marked BitCodec.naturalCode (a.2.map Fin.val) =
      BitCodec.integerCode a.1 ++ (SparseListCodec.list (SparseListCodec.finite n)).code a.2
    rw [RowWordCodec.marked_map]
    exact congrArg (List.append (BitCodec.integerCode a.1)) (RowWordCodec.marked_codec (SparseListCodec.finite n) a.2)

theorem numericRows_finite (n : ℕ) (ps : List (Poly (Fin n))) :
    numericRows (ps.map (relabel Fin.val)) = (SparseListCodec.list (SparsePolynomialCodec.polynomial n)).code ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    change true :: (numericPolynomial (relabel Fin.val p) ++ numericRows (rest.map (relabel Fin.val))) =
      true :: ((SparsePolynomialCodec.polynomial n).code p ++
        (SparseListCodec.list (SparsePolynomialCodec.polynomial n)).code rest)
    rw [numericPolynomial_finite, ih]

end JointThermoComplexity.Complexity.PreorderRowCode

#print axioms JointThermoComplexity.Complexity.PreorderRowCode.normalized_eq
#print axioms JointThermoComplexity.Complexity.PreorderRowCode.numericRows_finite
