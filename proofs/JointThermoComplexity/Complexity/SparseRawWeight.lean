module
public import proofs.JointThermoComplexity.Complexity.SparseIntegerPolynomial

set_option autoImplicit false
@[expose] public section

/-! # Computable coefficient norm before cancellation

This norm sums the absolute values of the actual stored coefficients. It
therefore bounds each emitted integer even when repeated monomials cancel
in the algebraic interpretation. It does not assume canonical support data.
-/

namespace JointThermoComplexity.Complexity.SparseInteger
variable {V W : Type}

def rawWeight (p : Poly V) : ℕ := (p.map (fun a => a.1.natAbs)).sum

@[simp] theorem rawWeight_nil : rawWeight ([] : Poly V) = 0 := rfl

@[simp] theorem rawWeight_cons (a : ℤ × List V) (p : Poly V) :
    rawWeight (a :: p) = a.1.natAbs + rawWeight p := rfl

theorem rawWeight_append (p q : Poly V) : rawWeight (p ++ q) = rawWeight p + rawWeight q := by
  simp only [rawWeight, List.map_append, List.sum_append]

@[simp] theorem rawWeight_constant (c : ℤ) : rawWeight (constant (V := V) c) = c.natAbs := by
  simp [constant]

@[simp] theorem rawWeight_atom (v : V) : rawWeight (atom v) = 1 := by
  simp [atom]

@[simp] theorem rawWeight_add (p q : Poly V) : rawWeight (add p q) = rawWeight p + rawWeight q :=
  rawWeight_append p q

@[simp] theorem rawWeight_scale (c : ℤ) (p : Poly V) : rawWeight (scale c p) = c.natAbs * rawWeight p := by
  induction p with
  | nil => simp [scale]
  | cons a p ih =>
    change (c * a.1).natAbs + rawWeight (scale c p) = c.natAbs * (a.1.natAbs + rawWeight p)
    rw [Int.natAbs_mul, ih, Nat.mul_add]

@[simp] theorem rawWeight_neg (p : Poly V) : rawWeight (neg p) = rawWeight p := by
  rw [neg, rawWeight_scale]
  simp

@[simp] theorem rawWeight_sub (p q : Poly V) : rawWeight (sub p q) = rawWeight p + rawWeight q := by
  rw [sub, rawWeight_add, rawWeight_neg]

@[simp] theorem rawWeight_relabel (f : V → W) (p : Poly V) : rawWeight (relabel f p) = rawWeight p := by
  simp only [rawWeight, relabel, List.map_map, Function.comp_def]

theorem rawWeight_monomial_product (a : ℤ × List V) (q : Poly V) :
    rawWeight (q.map (fun b => (a.1 * b.1, a.2 ++ b.2))) = a.1.natAbs * rawWeight q := by
  induction q with
  | nil => simp
  | cons b q ih =>
    change (a.1 * b.1).natAbs + rawWeight (q.map (fun b => (a.1 * b.1, a.2 ++ b.2))) =
      a.1.natAbs * (b.1.natAbs + rawWeight q)
    rw [Int.natAbs_mul, ih, Nat.mul_add]

@[simp] theorem rawWeight_product (p q : Poly V) : rawWeight (product p q) = rawWeight p * rawWeight q := by
  induction p with
  | nil => simp [product]
  | cons a p ih =>
    change rawWeight (q.map (fun b => (a.1 * b.1, a.2 ++ b.2)) ++ product p q) =
      (a.1.natAbs + rawWeight p) * rawWeight q
    rw [rawWeight_append, rawWeight_monomial_product, ih, Nat.add_mul]

@[simp] theorem rawWeight_square (p : Poly V) : rawWeight (square p) = rawWeight p ^ 2 := by
  rw [square, rawWeight_product, pow_two]

theorem rawWeight_member (p : Poly V) (a : ℤ × List V) (ha : a ∈ p) : a.1.natAbs ≤ rawWeight p := by
  induction p generalizing a with
  | nil => simp at ha
  | cons b p ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [rawWeight_cons]
      exact Nat.le_add_right _ _
    · have h := ih a ha
      rw [rawWeight_cons]
      omega

end JointThermoComplexity.Complexity.SparseInteger

#print axioms JointThermoComplexity.Complexity.SparseInteger.rawWeight_scale
#print axioms JointThermoComplexity.Complexity.SparseInteger.rawWeight_product
#print axioms JointThermoComplexity.Complexity.SparseInteger.rawWeight_relabel
#print axioms JointThermoComplexity.Complexity.SparseInteger.rawWeight_member
