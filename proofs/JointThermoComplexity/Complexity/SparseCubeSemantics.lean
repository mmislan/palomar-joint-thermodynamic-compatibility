module
public import proofs.JointThermoComplexity.Complexity.SparseSubstitutionSemantics

set_option autoImplicit false
@[expose] public section

/-! Integer denominator clearing for the affine half-cube transformation. -/

namespace JointThermoComplexity.Complexity.SparseSubstitution
open SparseInteger
variable {V : Type}

theorem shifted_product (x : V → ℝ) (vs : List V) :
    (vs.map (fun v => 2 * x v - 3)).prod =
      (2 : ℝ) ^ vs.length * (vs.map (fun v => x v - 3 / 2)).prod := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, ih]
    ring

theorem eval_cubeTerm (d : ℕ) (a : ℤ × List V) (hd : a.2.length ≤ d) (x : V → ℝ) :
    (interpret (cubeTerm d a)).eval₂ (Int.castRingHom ℝ) x =
      (2 : ℝ) ^ d * ((a.1 : ℝ) * (a.2.map (fun v => x v - 3 / 2)).prod) := by
  rw [cubeTerm, interpret_scale, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
  simp only [Int.coe_castRingHom, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, eval_expand, eval_cubeVariable]
  rw [shifted_product]
  have he : (2 : ℝ) ^ (d - a.2.length) * 2 ^ a.2.length = 2 ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  calc
    ((a.1 : ℝ) * 2 ^ (d - a.2.length)) *
        (2 ^ a.2.length * (a.2.map (fun v => x v - 3 / 2)).prod) =
        (2 ^ (d - a.2.length) * 2 ^ a.2.length) *
          ((a.1 : ℝ) * (a.2.map (fun v => x v - 3 / 2)).prod) := by ring
    _ = _ := by rw [he]

theorem eval_cube (d : ℕ) (p : Poly V) (hp : DegreeLE d p) (x : V → ℝ) :
    (interpret (cube d p)).eval₂ (Int.castRingHom ℝ) x =
      (2 : ℝ) ^ d * (interpret p).eval₂ (Int.castRingHom ℝ) (fun v => x v - 3 / 2) := by
  induction p with
  | nil => simp
  | cons a p ih =>
    rw [cube_cons, interpret_append, MvPolynomial.eval₂_add,
      eval_cubeTerm d a (hp a List.mem_cons_self), ih (fun t ht => hp t (List.mem_cons_of_mem a ht))]
    simp only [interpret_cons, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, Int.coe_castRingHom, eval_monomial]
    ring

end JointThermoComplexity.Complexity.SparseSubstitution

#print axioms JointThermoComplexity.Complexity.SparseSubstitution.eval_cubeTerm
#print axioms JointThermoComplexity.Complexity.SparseSubstitution.eval_cube
