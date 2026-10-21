module
public import proofs.JointThermoComplexity.Complexity.SparseIntegerPolynomial
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Flatten

set_option autoImplicit false
@[expose] public section

/-! # Executable sparse sums of squares and strict integer polynomials

Finite lists are constructed explicitly with List.ofFn. The bounds below
count raw terms before cancellations; they are distinct from the earlier
canonical coefficient bounds and from a binary Turing runtime theorem.
-/

namespace JointThermoComplexity.Complexity.SparseStrictPolynomial
open SparseInteger
variable {V : Type} {n : ℕ}

def sumFamily (q : Fin n → Poly V) : Poly V := (List.ofFn q).flatten
def energy (q : Fin n → Poly V) : Poly V := sumFamily (fun j => square (q j))

def edge (k : ℕ) (i : Fin (k + 1)) : Poly (Fin (k + 1)) :=
  Fin.cases (sub (scale 16 (atom 0)) (constant 1))
    (fun j => scale 16 (sub (atom j.succ) (square (atom j.castSucc)))) i

def error (k : ℕ) : Poly (Fin (k + 1)) := energy (edge k)

def bounded (q : Fin n → Poly V) (k : ℕ) : Poly (V ⊕ Fin (k + 1)) :=
  sub (sub (scale 256 (square (atom (.inr (Fin.last k))))) (scale 256 (relabel Sum.inl (energy q))))
    (scale 400 (relabel Sum.inr (error k)))

def allReal (q : Fin n → Poly V) (k : ℕ) : Poly (V ⊕ Fin (k + 1)) :=
  sub (sub (scale 256 (product (square (atom (.inr (Fin.last k))))
    (sub (constant 1) (square (atom (.inr (Fin.last k))))))) (scale 256 (relabel Sum.inl (energy q))))
    (scale 400 (relabel Sum.inr (error k)))

private theorem degree_mono {a b : ℕ} {p : Poly V} (hab : a ≤ b) (hp : DegreeLE a p) : DegreeLE b p :=
  fun t ht => Nat.le_trans (hp t ht) hab

theorem sumFamily_degree {d : ℕ} (q : Fin n → Poly V) (hq : ∀ j, DegreeLE d (q j)) :
    DegreeLE d (sumFamily q) := by
  intro t ht
  obtain ⟨p, hp, ht⟩ := List.mem_flatten.mp ht
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  exact hq j t ht

private theorem flatten_length_le (ps : List (Poly V)) (B : ℕ) (hB : ∀ p ∈ ps, p.length ≤ B) :
    ps.flatten.length ≤ ps.length * B := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp := hB p List.mem_cons_self
    have ht := ih (fun q hq => hB q (List.mem_cons_of_mem p hq))
    change (p ++ ps.flatten).length ≤ (ps.length + 1) * B
    rw [List.length_append, Nat.add_mul, Nat.one_mul]
    omega

theorem sumFamily_length (q : Fin n → Poly V) (B : ℕ) (hB : ∀ j, (q j).length ≤ B) :
    (sumFamily q).length ≤ n * B := by
  have h : ∀ p ∈ List.ofFn q, p.length ≤ B := by
    intro p hp
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
    exact hB j
  simpa only [sumFamily, List.length_ofFn] using flatten_length_le (List.ofFn q) B h

theorem energy_degree (q : Fin n → Poly V) (hq : ∀ j, DegreeLE 2 (q j)) : DegreeLE 4 (energy q) :=
  sumFamily_degree _ (fun j => degree_square (hq j))

theorem energy_length (q : Fin n → Poly V) (B : ℕ) (hB : ∀ j, (q j).length ≤ B) :
    (energy q).length ≤ n * B ^ 2 := by
  apply sumFamily_length _ (B ^ 2)
  intro j
  rw [length_square]
  exact Nat.pow_le_pow_left (hB j) 2

theorem edge_degree (k : ℕ) (i : Fin (k + 1)) : DegreeLE 2 (edge k i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact degree_sub (degree_scale 16 (degree_mono (by decide : 1 ≤ 2) (degree_atom 0)))
      (degree_mono (by decide : 0 ≤ 2) (degree_constant 1))
  · exact degree_scale 16 (degree_sub (degree_mono (by decide : 1 ≤ 2) (degree_atom j.succ))
      (degree_square (degree_atom j.castSucc)))

theorem edge_length (k : ℕ) (i : Fin (k + 1)) : (edge k i).length = 2 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [edge]
  · simp [edge, length_square]

theorem error_degree (k : ℕ) : DegreeLE 4 (error k) := energy_degree _ (edge_degree k)

theorem error_length (k : ℕ) : (error k).length ≤ (k + 1) * 4 := by
  apply energy_length (edge k) 2
  intro i
  exact Nat.le_of_eq (edge_length k i)

theorem bounded_degree (q : Fin n → Poly V) (hq : ∀ j, DegreeLE 2 (q j)) (k : ℕ) : DegreeLE 4 (bounded q k) := by
  apply degree_sub
  · apply degree_sub
    · exact degree_mono (by decide : 2 ≤ 4) (degree_scale 256 (degree_square (degree_atom _)))
    · exact degree_scale 256 (degree_relabel _ (energy_degree q hq))
  · exact degree_scale 400 (degree_relabel _ (error_degree k))

theorem allReal_degree (q : Fin n → Poly V) (hq : ∀ j, DegreeLE 2 (q j)) (k : ℕ) : DegreeLE 4 (allReal q k) := by
  apply degree_sub
  · apply degree_sub
    · exact degree_scale 256 (degree_product (degree_square (degree_atom _))
        (degree_sub (degree_mono (by decide : 0 ≤ 2) (degree_constant 1)) (degree_square (degree_atom _))))
    · exact degree_scale 256 (degree_relabel _ (energy_degree q hq))
  · exact degree_scale 400 (degree_relabel _ (error_degree k))

theorem bounded_length (q : Fin n → Poly V) (B : ℕ) (hB : ∀ j, (q j).length ≤ B) (k : ℕ) :
    (bounded q k).length ≤ 1 + n * B ^ 2 + 4 * (k + 1) := by
  have hE := energy_length q B hB
  have he := error_length k
  simp only [bounded, length_sub, length_scale, length_relabel, length_square, length_atom]
  omega

theorem allReal_length (q : Fin n → Poly V) (B : ℕ) (hB : ∀ j, (q j).length ≤ B) (k : ℕ) :
    (allReal q k).length ≤ 2 + n * B ^ 2 + 4 * (k + 1) := by
  have hE := energy_length q B hB
  have he := error_length k
  simp only [allReal, length_sub, length_scale, length_relabel, length_product, length_square, length_atom, length_constant]
  omega

end JointThermoComplexity.Complexity.SparseStrictPolynomial

#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.bounded
#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.bounded_degree
#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.allReal_degree
#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.bounded_length
#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.allReal_length
