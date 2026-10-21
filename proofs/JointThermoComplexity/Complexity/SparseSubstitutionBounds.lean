module
public import proofs.JointThermoComplexity.Complexity.SparseSubstitution
public import proofs.JointThermoComplexity.Complexity.SparseStoredCoefficients

set_option autoImplicit false
@[expose] public section

/-! Raw size, degree and coefficient bounds for executable coordinate expansion.
These bounds concern stored lists before any cancellation. -/

namespace JointThermoComplexity.Complexity.SparseSubstitution
open SparseInteger
variable {V W : Type}

theorem degree_mono {a b : ℕ} {p : Poly V} (hab : a ≤ b) (hp : DegreeLE a p) : DegreeLE b p :=
  fun t ht => (hp t ht).trans hab

theorem degree_expand (f : V → Poly W) (hf : ∀ v, DegreeLE 1 (f v)) (vs : List V) :
    DegreeLE vs.length (expand f vs) := by
  induction vs with
  | nil => exact degree_constant 1
  | cons v vs ih =>
    simpa only [expand_cons, List.length_cons, Nat.add_comm] using degree_product (hf v) ih

theorem degree_substitute (f : V → Poly W) (hf : ∀ v, DegreeLE 1 (f v))
    {d : ℕ} (p : Poly V) (hp : DegreeLE d p) : DegreeLE d (substitute f p) := by
  induction p with
  | nil => simp [DegreeLE]
  | cons a p ih =>
    exact degree_add (degree_mono (hp a List.mem_cons_self) (degree_scale a.1 (degree_expand f hf a.2)))
      (ih (fun t ht => hp t (List.mem_cons_of_mem a ht)))

theorem length_expand (f : V → Poly W) (hf : ∀ v, (f v).length ≤ 2) (vs : List V) :
    (expand f vs).length ≤ 2 ^ vs.length := by
  induction vs with
  | nil => simp [expand, constant]
  | cons v vs ih =>
    rw [expand_cons, length_product, List.length_cons, pow_succ]
    exact (Nat.mul_le_mul (hf v) ih).trans_eq (Nat.mul_comm _ _)

theorem length_substitute (f : V → Poly W) (hf : ∀ v, (f v).length ≤ 2)
    {d : ℕ} (p : Poly V) (hp : DegreeLE d p) :
    (substitute f p).length ≤ p.length * 2 ^ d := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ha := (length_expand f hf a.2).trans
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (hp a List.mem_cons_self))
    have ht := ih (fun t ht => hp t (List.mem_cons_of_mem a ht))
    rw [substitute_cons, List.length_append, length_scale]
    exact (Nat.add_le_add ha ht).trans_eq (by simp [Nat.add_mul, Nat.add_comm])

theorem coefficients_product {A B : ℕ} {p q : Poly V}
    (hp : CoefficientsLE A p) (hq : CoefficientsLE B q) : CoefficientsLE (A * B) (product p q) := by
  intro t ht
  obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  change (a.1 * b.1).natAbs ≤ A * B
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul (hp a ha) (hq b hb)

theorem coefficients_expand (f : V → Poly W) {K : ℕ} (hf : ∀ v, CoefficientsLE K (f v)) (vs : List V) :
    CoefficientsLE (K ^ vs.length) (expand f vs) := by
  induction vs with
  | nil => simp [expand, CoefficientsLE, constant]
  | cons v vs ih =>
    simpa only [expand_cons, List.length_cons, pow_succ, Nat.mul_comm] using coefficients_product (hf v) ih

theorem coefficients_substitute (f : V → Poly W) {C K d : ℕ} (hK : 1 ≤ K)
    (hf : ∀ v, CoefficientsLE K (f v)) (p : Poly V)
    (hp : DegreeLE d p) (hc : CoefficientsLE C p) : CoefficientsLE (C * K ^ d) (substitute f p) := by
  induction p with
  | nil => simp [CoefficientsLE]
  | cons a p ih =>
    apply coefficients_add
    · exact coefficients_mono
        (Nat.mul_le_mul (hc a List.mem_cons_self)
          (Nat.pow_le_pow_right hK (hp a List.mem_cons_self)))
        (coefficients_scale a.1 (coefficients_expand f hf a.2))
    · exact ih (fun t ht => hp t (List.mem_cons_of_mem a ht))
        (fun t ht => hc t (List.mem_cons_of_mem a ht))

theorem cubeVariable_degree (v : V) : DegreeLE 1 (cubeVariable v) := by
  simp [DegreeLE, cubeVariable]

theorem orthantVariable_degree (v : V) : DegreeLE 1 (orthantVariable v) := by
  simp [DegreeLE, orthantVariable]

theorem cubeVariable_coefficients (v : V) : CoefficientsLE 3 (cubeVariable v) := by
  simp [CoefficientsLE, cubeVariable]

theorem orthantVariable_coefficients (v : V) : CoefficientsLE 1 (orthantVariable v) := by
  simp [CoefficientsLE, orthantVariable]

theorem degree_cube {d : ℕ} (p : Poly V) (hp : DegreeLE d p) : DegreeLE d (cube d p) := by
  induction p with
  | nil => simp [DegreeLE]
  | cons a p ih =>
    exact degree_add (degree_scale _ (degree_mono (hp a List.mem_cons_self)
      (degree_expand cubeVariable cubeVariable_degree a.2)))
      (ih (fun t ht => hp t (List.mem_cons_of_mem a ht)))

theorem degree_orthant {d : ℕ} (p : Poly V) (hp : DegreeLE d p) : DegreeLE d (orthant p) :=
  degree_substitute orthantVariable orthantVariable_degree p hp

theorem length_cube_eq (d : ℕ) (p : Poly V) : (cube d p).length = (substitute cubeVariable p).length := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [cube_cons, substitute_cons, List.length_append, cubeTerm, length_scale, ih]

theorem length_cube {d : ℕ} (p : Poly V) (hp : DegreeLE d p) : (cube d p).length ≤ p.length * 2 ^ d := by
  rw [length_cube_eq]
  exact length_substitute cubeVariable (fun _ => by simp [cubeVariable]) p hp

theorem length_orthant {d : ℕ} (p : Poly V) (hp : DegreeLE d p) : (orthant p).length ≤ p.length * 2 ^ d :=
  length_substitute orthantVariable (fun _ => by simp [orthantVariable]) p hp

theorem coefficients_cubeTerm {C d : ℕ} (a : ℤ × List V)
    (hc : a.1.natAbs ≤ C) (hd : a.2.length ≤ d) : CoefficientsLE (C * 2 ^ d * 3 ^ d) (cubeTerm d a) := by
  apply coefficients_mono _ (coefficients_scale _ (coefficients_expand cubeVariable cubeVariable_coefficients a.2))
  simpa only [Int.natAbs_mul, Int.natAbs_pow, show (2 : ℤ).natAbs = 2 from rfl] using
    Nat.mul_le_mul (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.sub_le d a.2.length)))
      (Nat.pow_le_pow_right (by decide : 1 ≤ 3) hd)

theorem coefficients_cube {C d : ℕ} (p : Poly V) (hp : DegreeLE d p) (hc : CoefficientsLE C p) :
    CoefficientsLE (C * 2 ^ d * 3 ^ d) (cube d p) := by
  induction p with
  | nil => simp [CoefficientsLE]
  | cons a p ih =>
    exact coefficients_add (coefficients_cubeTerm a (hc a List.mem_cons_self) (hp a List.mem_cons_self))
      (ih (fun t ht => hp t (List.mem_cons_of_mem a ht)) (fun t ht => hc t (List.mem_cons_of_mem a ht)))

theorem coefficients_orthant {C d : ℕ} (p : Poly V) (hp : DegreeLE d p) (hc : CoefficientsLE C p) :
    CoefficientsLE C (orthant p) := by
  simpa only [orthant, one_pow, Nat.mul_one] using
    coefficients_substitute orthantVariable (by decide : 1 ≤ 1) orthantVariable_coefficients p hp hc

end JointThermoComplexity.Complexity.SparseSubstitution

#print axioms JointThermoComplexity.Complexity.SparseSubstitution.degree_cube
#print axioms JointThermoComplexity.Complexity.SparseSubstitution.degree_orthant
#print axioms JointThermoComplexity.Complexity.SparseSubstitution.length_cube
#print axioms JointThermoComplexity.Complexity.SparseSubstitution.coefficients_cube
#print axioms JointThermoComplexity.Complexity.SparseSubstitution.coefficients_orthant
