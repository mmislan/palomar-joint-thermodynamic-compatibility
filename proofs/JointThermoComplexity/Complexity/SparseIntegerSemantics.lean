module
public import proofs.JointThermoComplexity.Complexity.SparseIntegerPolynomial
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

set_option autoImplicit false
@[expose] public section

/-! # Exact algebraic interpretation of executable polynomial lists

Zero terms and repeated monomials are handled by the sum interpretation. The
data operations remain executable; only their mathematical interpretation
uses Mathlib's multivariate-polynomial representation.
-/

namespace JointThermoComplexity.Complexity.SparseInteger
variable {V W : Type}

noncomputable def monomial (vs : List V) : MvPolynomial V ℤ := (vs.map MvPolynomial.X).prod
noncomputable def interpret (p : Poly V) : MvPolynomial V ℤ :=
  (p.map (fun t => MvPolynomial.C t.1 * monomial t.2)).sum

@[simp] theorem monomial_nil : monomial ([] : List V) = 1 := rfl
@[simp] theorem monomial_cons (v : V) (vs : List V) :
    monomial (v :: vs) = MvPolynomial.X v * monomial vs := rfl

theorem monomial_append (us vs : List V) : monomial (us ++ vs) = monomial us * monomial vs := by
  simp only [monomial, List.map_append, List.prod_append]

@[simp] theorem interpret_nil : interpret ([] : Poly V) = 0 := rfl
@[simp] theorem interpret_cons (a : ℤ × List V) (p : Poly V) :
    interpret (a :: p) = MvPolynomial.C a.1 * monomial a.2 + interpret p := rfl

theorem interpret_append (p q : Poly V) : interpret (p ++ q) = interpret p + interpret q := by
  simp only [interpret, List.map_append, List.sum_append]

theorem interpret_constant (c : ℤ) : interpret (constant (V := V) c) = MvPolynomial.C c := by
  simp only [constant, interpret_cons, interpret_nil, monomial_nil, mul_one, add_zero]

theorem interpret_atom (v : V) : interpret (atom v) = MvPolynomial.X v := by
  simp [atom, monomial_cons]

theorem interpret_add (p q : Poly V) : interpret (add p q) = interpret p + interpret q := interpret_append p q

theorem interpret_scale (c : ℤ) (p : Poly V) : interpret (scale c p) = MvPolynomial.C c * interpret p := by
  induction p with
  | nil => simp [scale]
  | cons a p ih =>
    change MvPolynomial.C (c * a.1) * monomial a.2 + interpret (scale c p) =
      MvPolynomial.C c * (MvPolynomial.C a.1 * monomial a.2 + interpret p)
    rw [map_mul, ih]
    ring

theorem interpret_neg (p : Poly V) : interpret (neg p) = -interpret p := by
  rw [neg, interpret_scale]
  simp

theorem interpret_sub (p q : Poly V) : interpret (sub p q) = interpret p - interpret q := by
  rw [sub, interpret_add, interpret_neg, sub_eq_add_neg]

theorem interpret_monomial_product (a : ℤ × List V) (q : Poly V) :
    interpret (q.map (fun b => (a.1 * b.1, a.2 ++ b.2))) =
      (MvPolynomial.C a.1 * monomial a.2) * interpret q := by
  induction q with
  | nil => simp
  | cons b q ih =>
    change MvPolynomial.C (a.1 * b.1) * monomial (a.2 ++ b.2) +
      interpret (q.map (fun b => (a.1 * b.1, a.2 ++ b.2))) =
        (MvPolynomial.C a.1 * monomial a.2) * (MvPolynomial.C b.1 * monomial b.2 + interpret q)
    rw [map_mul, monomial_append, ih]
    ring

theorem interpret_product (p q : Poly V) : interpret (product p q) = interpret p * interpret q := by
  induction p with
  | nil => simp [product]
  | cons a p ih =>
    change interpret (q.map (fun b => (a.1 * b.1, a.2 ++ b.2)) ++ product p q) =
      (MvPolynomial.C a.1 * monomial a.2 + interpret p) * interpret q
    rw [interpret_append, interpret_monomial_product, ih, add_mul]

theorem interpret_square (p : Poly V) : interpret (square p) = interpret p ^ 2 := by
  rw [square, interpret_product, pow_two]

theorem monomial_relabel (f : V → W) (vs : List V) :
    MvPolynomial.rename f (monomial vs) = monomial (vs.map f) := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp only [monomial_cons, List.map_cons, map_mul, MvPolynomial.rename_X, ih]

theorem interpret_relabel (f : V → W) (p : Poly V) :
    interpret (relabel f p) = MvPolynomial.rename f (interpret p) := by
  induction p with
  | nil => simp [relabel]
  | cons a p ih =>
    change MvPolynomial.C a.1 * monomial (a.2.map f) + interpret (relabel f p) =
      MvPolynomial.rename f (MvPolynomial.C a.1 * monomial a.2 + interpret p)
    rw [map_add, map_mul, MvPolynomial.rename_C, monomial_relabel, ih]

theorem eval_monomial (x : V → ℝ) (vs : List V) :
    (monomial vs).eval₂ (Int.castRingHom ℝ) x = (vs.map x).prod := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp only [monomial_cons, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      List.map_cons, List.prod_cons, ih]

theorem eval_interpret (x : V → ℝ) (p : Poly V) :
    (interpret p).eval₂ (Int.castRingHom ℝ) x = (p.map (fun a => (a.1 : ℝ) * (a.2.map x).prod)).sum := by
  induction p with
  | nil => simp
  | cons a p ih => simp only [interpret_cons, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, Int.coe_castRingHom, eval_monomial, List.map_cons, List.sum_cons, ih]

theorem monomial_degree (vs : List V) : (monomial vs).totalDegree ≤ vs.length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    rw [monomial_cons, List.length_cons]
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa only [MvPolynomial.totalDegree_X, Nat.add_comm] using Nat.add_le_add_left ih 1)

theorem interpret_degree {d : ℕ} (p : Poly V) (hp : DegreeLE d p) : (interpret p).totalDegree ≤ d := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ha := hp a List.mem_cons_self
    have htail : DegreeLE d p := fun t ht => hp t (List.mem_cons_of_mem a ht)
    have hterm : (MvPolynomial.C a.1 * monomial a.2).totalDegree ≤ d := by
      apply (MvPolynomial.totalDegree_mul _ _).trans
      simpa only [MvPolynomial.totalDegree_C, zero_add] using (monomial_degree a.2).trans ha
    rw [interpret_cons]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le hterm (ih htail))

end JointThermoComplexity.Complexity.SparseInteger

#print axioms JointThermoComplexity.Complexity.SparseInteger.interpret_product
#print axioms JointThermoComplexity.Complexity.SparseInteger.interpret_relabel
#print axioms JointThermoComplexity.Complexity.SparseInteger.eval_interpret
#print axioms JointThermoComplexity.Complexity.SparseInteger.interpret_degree
