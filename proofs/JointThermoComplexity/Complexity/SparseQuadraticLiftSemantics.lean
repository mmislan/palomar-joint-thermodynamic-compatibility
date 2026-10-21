module
public import proofs.JointThermoComplexity.Complexity.SparseQuadraticLift
public import proofs.JointThermoComplexity.Complexity.SparseIntegerSemantics
public import proofs.JointThermoComplexity.Complexity.QuadraticHomogenization

set_option autoImplicit false
@[expose] public section

/-! # Exact agreement of executable and algebraic quadratic homogenization -/

namespace JointThermoComplexity.Complexity.SparseQuadraticLift
open SparseInteger
variable {V W : Type}

theorem monomial_replicate (n : ℕ) (v : V) : monomial (List.replicate n v) = MvPolynomial.X v ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, monomial_cons, ih, pow_succ']

theorem monomial_homogeneous (vs : List V) : (monomial vs).IsHomogeneous vs.length := by
  induction vs with
  | nil => exact MvPolynomial.isHomogeneous_one V ℤ
  | cons v vs ih =>
    simpa only [monomial_cons, List.length_cons, Nat.add_comm] using (MvPolynomial.isHomogeneous_X ℤ v).mul ih

theorem quadraticLift_add (p q : MvPolynomial V ℤ) :
    QuadraticHomogenization.quadraticLift (p + q) =
      QuadraticHomogenization.quadraticLift p + QuadraticHomogenization.quadraticLift q := by
  simp only [QuadraticHomogenization.quadraticLift, map_add]
  ring

theorem term_as_product (a : ℤ × List V) (ha : a.2.length ≤ 2) :
    interpret (term a) = MvPolynomial.rename Sum.inl (MvPolynomial.C a.1 * monomial a.2) *
      MvPolynomial.X (Sum.inr ()) ^ (2 - a.2.length) := by
  rw [term, ite_eq_left ha]
  simp only [interpret_cons, interpret_nil, add_zero, monomial_append, monomial_replicate]
  rw [← monomial_relabel (Sum.inl : V → V ⊕ Unit), map_mul, MvPolynomial.rename_C]
  ring

theorem interpret_term (a : ℤ × List V) :
    interpret (term a) = QuadraticHomogenization.quadraticLift (MvPolynomial.C a.1 * monomial a.2) := by
  have hh := (monomial_homogeneous a.2).C_mul a.1
  have h0 := MvPolynomial.homogeneousComponent_of_mem (m := 0) hh
  have h1 := MvPolynomial.homogeneousComponent_of_mem (m := 1) hh
  have h2 := MvPolynomial.homogeneousComponent_of_mem (m := 2) hh
  by_cases ha : a.2.length ≤ 2
  · rw [term_as_product a ha, QuadraticHomogenization.quadraticLift, h0, h1, h2]
    have hc : a.2.length = 0 ∨ a.2.length = 1 ∨ a.2.length = 2 := by omega
    rcases hc with h | h | h <;> simp [h]
  · have hi0 : 0 ≠ a.2.length := by omega
    have hi1 : 1 ≠ a.2.length := by omega
    have hi2 : 2 ≠ a.2.length := by omega
    simp only [term, ite_eq_right ha, interpret_nil, QuadraticHomogenization.quadraticLift,
      h0, h1, h2, ite_eq_right hi0, ite_eq_right hi1, ite_eq_right hi2, map_zero, zero_mul, zero_add]

theorem interpret_lift (p : Poly V) :
    interpret (lift p) = QuadraticHomogenization.quadraticLift (interpret p) := by
  induction p with
  | nil => simp [lift, QuadraticHomogenization.quadraticLift]
  | cons a p ih =>
    change interpret (term a ++ lift p) =
      QuadraticHomogenization.quadraticLift (MvPolynomial.C a.1 * monomial a.2 + interpret p)
    rw [interpret_append, quadraticLift_add, interpret_term, ih]

theorem interpreted_degree (p : Poly V) : (interpret (lift p)).totalDegree ≤ 2 :=
  SparseInteger.interpret_degree (lift p) (lift_degree p)

theorem eval_lift_scaled (p : Poly V) (hp : (interpret p).totalDegree ≤ 2) (x : V → ℝ) (s : ℝ) :
    (interpret (lift p)).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (fun i => s * x i) (fun _ => s)) = s ^ 2 * (interpret p).eval₂ (Int.castRingHom ℝ) x := by
  rw [interpret_lift]
  exact QuadraticHomogenization.eval_quadraticLift_scaled _ hp x s

theorem eval_lift_zero_iff (p : Poly V) (hp : (interpret p).totalDegree ≤ 2)
    (u : V → ℝ) (s : ℝ) (hs : s ≠ 0) :
    (interpret (lift p)).eval₂ (Int.castRingHom ℝ) (Sum.elim u (fun _ => s)) = 0 ↔
      (interpret p).eval₂ (Int.castRingHom ℝ) (fun i => u i / s) = 0 := by
  rw [interpret_lift]
  exact QuadraticHomogenization.quadraticLift_zero_iff _ hp u s hs

theorem quadraticLift_rename (f : V → W) (p : MvPolynomial V ℤ) :
    QuadraticHomogenization.quadraticLift (MvPolynomial.rename f p) =
      MvPolynomial.rename (Sum.map f id) (QuadraticHomogenization.quadraticLift p) := by
  simp only [QuadraticHomogenization.quadraticLift, ← MvPolynomial.rename_homogeneousComponent,
    map_add, map_mul, map_pow, MvPolynomial.rename_X, MvPolynomial.rename_rename]
  rfl

end JointThermoComplexity.Complexity.SparseQuadraticLift

#print axioms JointThermoComplexity.Complexity.SparseQuadraticLift.interpret_lift
#print axioms JointThermoComplexity.Complexity.SparseQuadraticLift.interpreted_degree
#print axioms JointThermoComplexity.Complexity.SparseQuadraticLift.eval_lift_zero_iff
#print axioms JointThermoComplexity.Complexity.SparseQuadraticLift.quadraticLift_rename
