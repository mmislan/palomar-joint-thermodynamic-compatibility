module
public import proofs.JointThermoComplexity.Complexity.SparsePolynomialCodec

set_option autoImplicit false
@[expose] public section

/-! Marked rows concatenate stored binary index words literally, retaining all raw terms. -/

namespace JointThermoComplexity.Complexity.RowWordCodec
open SparseInteger
variable {α β : Type}

def marked (f : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: rest => true :: (f a ++ marked f rest)

theorem marked_map (f : β → List Bool) (g : α → β) (xs : List α) :
    marked f (xs.map g) = marked (fun a => f (g a)) xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp only [List.map_cons, marked, ih]

theorem marked_codec (A : FiniteCodec.Codec α) (xs : List α) :
    marked A.code xs = (SparseListCodec.list A).code xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simpa only [marked, SparseListCodec.list, SparseListCodec.listCode] using congrArg (fun bits => true :: (A.code a ++ bits)) ih

def monomial (indices : List (List Bool)) : List Bool := marked id indices

def term (a : ℤ × List (List Bool)) : List Bool := BitCodec.integerCode a.1 ++ monomial a.2

def polynomial (p : Poly (List Bool)) : List Bool := marked term p

def rows (ps : List (Poly (List Bool))) : List Bool := marked polynomial ps

theorem monomial_finite (n : ℕ) (indices : List (Fin n)) :
    monomial (indices.map (fun i => BitCodec.naturalCode i.val)) =
      (SparseListCodec.list (SparseListCodec.finite n)).code indices := by
  rw [monomial, marked_map]
  exact marked_codec (SparseListCodec.finite n) indices

theorem term_finite (n : ℕ) (a : ℤ × List (Fin n)) :
    term (a.1, a.2.map (fun i => BitCodec.naturalCode i.val)) = (SparsePolynomialCodec.term n).code a := by
  rw [term, monomial_finite]
  rfl

theorem polynomial_finite (n : ℕ) (p : Poly (Fin n)) :
    polynomial (relabel (fun i => BitCodec.naturalCode i.val) p) = (SparsePolynomialCodec.polynomial n).code p := by
  induction p with
  | nil => rfl
  | cons a rest ih =>
    change true :: (term (a.1, a.2.map (fun i => BitCodec.naturalCode i.val)) ++
      polynomial (relabel (fun i => BitCodec.naturalCode i.val) rest)) =
        true :: ((SparsePolynomialCodec.term n).code a ++ (SparsePolynomialCodec.polynomial n).code rest)
    rw [term_finite, ih]

theorem rows_finite (n : ℕ) (ps : List (Poly (Fin n))) :
    rows (ps.map (relabel (fun i => BitCodec.naturalCode i.val))) =
      (SparseListCodec.list (SparsePolynomialCodec.polynomial n)).code ps := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    change true :: (polynomial (relabel (fun i => BitCodec.naturalCode i.val) p) ++
      rows (rest.map (relabel (fun i => BitCodec.naturalCode i.val)))) =
        true :: ((SparsePolynomialCodec.polynomial n).code p ++
          (SparseListCodec.list (SparsePolynomialCodec.polynomial n)).code rest)
    rw [polynomial_finite, ih]

theorem marked_length (f : α → List Bool) (xs : List α) :
    (marked f xs).length = xs.length + 1 + (xs.map (fun a => (f a).length)).sum := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [marked, List.length_cons, List.length_append, List.map_cons, List.sum_cons]
    rw [ih]
    omega

end JointThermoComplexity.Complexity.RowWordCodec

#print axioms JointThermoComplexity.Complexity.RowWordCodec.polynomial_finite
#print axioms JointThermoComplexity.Complexity.RowWordCodec.rows_finite
