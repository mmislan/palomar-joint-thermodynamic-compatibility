module
public import proofs.JointThermoComplexity.Complexity.SparseStrictPolynomial
public import Mathlib.Data.List.OfFn

set_option autoImplicit false
@[expose] public section

/-! Literal sparse section assembly. A list homomorphism distributes over
the ordered finite family without any permutation or coefficient cancellation.
-/

namespace JointThermoComplexity.Complexity.SparseSectionData
open SparseInteger
variable {V W : Type} {n : ℕ}

theorem map_flatten (F : Poly V → Poly W) (hnil : F [] = [])
    (happend : ∀ p q, F (p ++ q) = F p ++ F q) (ps : List (Poly V)) :
    F ps.flatten = (ps.map F).flatten := by
  induction ps with
  | nil => exact hnil
  | cons p ps ih => simp only [List.flatten_cons, happend, List.map_cons, ih]

theorem map_sumFamily (F : Poly V → Poly W) (hnil : F [] = [])
    (happend : ∀ p q, F (p ++ q) = F p ++ F q) (q : Fin n → Poly V) :
    F (SparseStrictPolynomial.sumFamily q) = SparseStrictPolynomial.sumFamily (fun j => F (q j)) := by
  unfold SparseStrictPolynomial.sumFamily
  rw [map_flatten F hnil happend, List.map_ofFn]
  rfl

theorem ofFn_append {α : Type} {a b : ℕ} (f : Fin a → α) (g : Fin b → α) :
    List.ofFn (Fin.append f g) = List.ofFn f ++ List.ofFn g := List.ofFn_fin_append f g

theorem ofFn_single {α : Type} (a : α) : List.ofFn (fun _ : Fin 1 => a) = [a] := rfl

end JointThermoComplexity.Complexity.SparseSectionData

#print axioms JointThermoComplexity.Complexity.SparseSectionData.map_sumFamily
#print axioms JointThermoComplexity.Complexity.SparseSectionData.ofFn_append
