module
public import proofs.JointThermoComplexity.PolynomialSource
public import proofs.JointThermoComplexity.Complexity.SparseIntegerSemantics
public import proofs.JointThermoComplexity.Complexity.SparseStoredCoefficients
public import Mathlib.Data.List.OfFn

set_option autoImplicit false
@[expose] public section

/-! Ordered raw coefficients and exponent counts agree with the original
chemical polynomial. No canonical support or duplicate removal is used. -/

namespace JointThermoComplexity.Complexity.RawChemicalPolynomial
open SparseInteger
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

def coefficientInteger (p : Poly V) (i : Fin p.length) : ℤ := p[i].1
noncomputable def coefficients (p : Poly V) (i : Fin p.length) : ℝ := coefficientInteger p i
def exponents (p : Poly V) (i : Fin p.length) (v : V) : ℕ := p[i].2.count v

theorem product_counts (vs : List V) (x : V → ℝ) :
    (vs.map x).prod = ∏ v, x v ^ vs.count v := by
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro v _ hv
  have hc : vs.count v = 0 := List.count_eq_zero_of_not_mem (by simpa only [List.mem_toFinset] using hv)
  simp only [hc, pow_zero]

theorem sum_counts (vs : List V) : (∑ v, vs.count v) = vs.length := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp [List.count_cons, Finset.sum_add_distrib, ih]

theorem polynomial_eval (p : Poly V) (x : V → ℝ) :
    Emitted.polynomial (coefficients p) (exponents p) x =
      (interpret p).eval₂ (Int.castRingHom ℝ) x := by
  rw [eval_interpret]
  unfold Emitted.polynomial coefficients coefficientInteger exponents
  simp_rw [← product_counts]
  simpa only [List.sum_ofFn, Fin.getElem_fin] using congrArg List.sum
    (List.ofFn_getElem_eq_map p (fun a => (a.1 : ℝ) * (a.2.map x).prod))

theorem exponent_sum (p : Poly V) (i : Fin p.length) : (∑ v, exponents p i v) = p[i].2.length :=
  sum_counts _

theorem exponent_bound {d : ℕ} (p : Poly V) (hp : DegreeLE d p) (i : Fin p.length) :
    (∑ v, exponents p i v) ≤ d := by
  rw [exponent_sum]
  exact hp _ (List.getElem_mem i.isLt)

omit [Fintype V] [DecidableEq V] in
theorem coefficient_bound {C : ℕ} (p : Poly V) (hp : CoefficientsLE C p) (i : Fin p.length) :
    (coefficientInteger p i).natAbs ≤ C := hp _ (List.getElem_mem i.isLt)

end JointThermoComplexity.Complexity.RawChemicalPolynomial

#print axioms JointThermoComplexity.Complexity.RawChemicalPolynomial.coefficientInteger
#print axioms JointThermoComplexity.Complexity.RawChemicalPolynomial.exponents
#print axioms JointThermoComplexity.Complexity.RawChemicalPolynomial.polynomial_eval
#print axioms JointThermoComplexity.Complexity.RawChemicalPolynomial.exponent_bound
