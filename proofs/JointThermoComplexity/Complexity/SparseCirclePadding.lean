module
public import proofs.JointThermoComplexity.Complexity.SparseIntegerPolynomial

set_option autoImplicit false
@[expose] public section

/-! # Executable integer circle padding, with raw list bounds

The mathematical coercivity and root-equivalence bridge is separate. These
definitions use only fixed integer constants and finite coordinate maps.
-/

namespace JointThermoComplexity.Complexity.SparseCirclePadding
open SparseInteger
variable {V A : Type}

def circle (i : V) : Poly (V × Bool) :=
  sub (scale 16 (add (square (atom (i, false))) (square (atom (i, true))))) (constant 1)

def family (q : A → Poly V) : A ⊕ V → Poly (V × Bool) :=
  Sum.elim (fun j => relabel (fun i => (i, false)) (q j)) circle

theorem circle_degree (i : V) : DegreeLE 2 (circle i) := by
  apply degree_sub (degree_scale 16 (degree_add (degree_square (degree_atom (i, false)))
    (degree_square (degree_atom (i, true)))))
  intro t ht
  exact Nat.le_trans (degree_constant 1 t ht) (by decide : 0 ≤ 2)

theorem family_degree (q : A → Poly V) (hq : ∀ j, DegreeLE 2 (q j)) (j : A ⊕ V) : DegreeLE 2 (family q j) := by
  cases j with
  | inl j => exact degree_relabel _ (hq j)
  | inr i => exact circle_degree i

theorem circle_length (i : V) : (circle i).length = 3 := by
  simp [circle, length_square]

theorem family_length (q : A → Poly V) (B : ℕ) (hB : ∀ j, (q j).length ≤ B) (j : A ⊕ V) :
    (family q j).length ≤ max B 3 := by
  cases j with
  | inl j =>
    change (relabel (fun i => (i, false)) (q j)).length ≤ _
    rw [length_relabel]
    exact Nat.le_trans (hB j) (Nat.le_max_left _ _)
  | inr i =>
    change (circle i).length ≤ _
    rw [circle_length]
    exact Nat.le_max_right _ _

end JointThermoComplexity.Complexity.SparseCirclePadding

#print axioms JointThermoComplexity.Complexity.SparseCirclePadding.family
#print axioms JointThermoComplexity.Complexity.SparseCirclePadding.family_degree
#print axioms JointThermoComplexity.Complexity.SparseCirclePadding.family_length
