module
public import proofs.JointThermoComplexity.Complexity.SparseIntegerPolynomial

set_option autoImplicit false
@[expose] public section

/-! # Executable quadratic homogenization of sparse integer lists

Each term of degree at most two is extended by copies of one shared scale
coordinate. Higher-degree terms are discarded, matching the algebraic
quadratic component operator. No coefficients or supports are enumerated.
-/

namespace JointThermoComplexity.Complexity.SparseQuadraticLift
open SparseInteger
variable {V : Type}

def term (a : ℤ × List V) : Poly (V ⊕ Unit) :=
  if a.2.length ≤ 2 then [(a.1, a.2.map Sum.inl ++ List.replicate (2 - a.2.length) (.inr ()))] else []

def lift (p : Poly V) : Poly (V ⊕ Unit) := p.flatMap term

theorem term_degree (a : ℤ × List V) : DegreeLE 2 (term a) := by
  intro t ht
  unfold term at ht
  split at ht
  next h =>
    have he := List.mem_singleton.mp ht
    rw [he]
    change (a.2.map (Sum.inl : V → V ⊕ Unit) ++ List.replicate (2 - a.2.length) (Sum.inr () : V ⊕ Unit)).length ≤ 2
    rw [List.length_append, List.length_map, List.length_replicate]
    omega
  next => simp at ht

theorem lift_degree (p : Poly V) : DegreeLE 2 (lift p) := by
  intro t ht
  obtain ⟨a, _, ht⟩ := List.mem_flatMap.mp ht
  exact term_degree a t ht

theorem term_length (a : ℤ × List V) : (term a).length ≤ 1 := by
  unfold term
  split <;> simp

theorem lift_length (p : Poly V) : (lift p).length ≤ p.length := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change (term a ++ lift p).length ≤ (a :: p).length
    rw [List.length_append, List.length_cons]
    have h := term_length a
    omega

end JointThermoComplexity.Complexity.SparseQuadraticLift

#print axioms JointThermoComplexity.Complexity.SparseQuadraticLift.lift_degree
#print axioms JointThermoComplexity.Complexity.SparseQuadraticLift.lift_length
