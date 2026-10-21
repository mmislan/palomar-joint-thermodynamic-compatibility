module
public import proofs.JointThermoComplexity.Complexity.StrictPositivityProblem
public import proofs.JointThermoComplexity.Complexity.SparsePositiveCoordinates
public import proofs.JointThermoComplexity.Complexity.SparseSubstitutionBounds
public import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
@[expose] public section

/-! Executable finite positive-coordinate data, exact verdict semantics and
raw size/degree/coefficient restrictions. Binary construction time is separate. -/

namespace JointThermoComplexity.Complexity.FinitePositiveCoordinates
open SparseInteger SparseSubstitution SparsePositiveCoordinates SparsePolynomialCodec

def data (boxed : Bool) (p : PolynomialData) : PolynomialData :=
  if boxed then ⟨p.arity, cube 4 p.payload⟩
  else ⟨p.arity + p.arity, relabel finSumFinEquiv (orthant p.payload)⟩

def code (boxed : Bool) (p : PolynomialData) : List Bool := SparsePolynomialCodec.code (data boxed p)

def Positive (boxed : Bool) (p : PolynomialData) : Prop :=
  if boxed then PositiveBox p.payload else PositiveOrthant p.payload

def Domain (p : PolynomialData) : Prop :=
  0 < p.arity ∧ DegreeLE 4 p.payload ∧ CoefficientsLE 530841600 p.payload

theorem data_domain (boxed : Bool) (p : PolynomialData) (hp : StrictPositivityProblem.Domain p) :
    Domain (data boxed p) := by
  obtain ⟨ha, hd, hc⟩ := hp
  cases boxed
  · exact ⟨by change 0 < p.arity + p.arity; omega,
      degree_relabel finSumFinEquiv (degree_orthant p.payload hd),
      coefficients_mono (by decide : 409600 ≤ 530841600)
        (coefficients_relabel finSumFinEquiv (coefficients_orthant p.payload hd hc))⟩
  · exact ⟨ha, degree_cube p.payload hd, coefficients_cube p.payload hd hc⟩

theorem arity_bound (boxed : Bool) (p : PolynomialData) : (data boxed p).arity ≤ 2 * p.arity := by
  cases boxed
  · change p.arity + p.arity ≤ 2 * p.arity
    omega
  · change p.arity ≤ 2 * p.arity
    omega

theorem length_bound (boxed : Bool) (p : PolynomialData) (hp : StrictPositivityProblem.Domain p) :
    (data boxed p).payload.length ≤ 16 * p.payload.length := by
  cases boxed
  · change (relabel finSumFinEquiv (orthant p.payload)).length ≤ 16 * p.payload.length
    rw [length_relabel]
    simpa only [show (2 : ℕ) ^ 4 = 16 from rfl, Nat.mul_comm] using length_orthant p.payload hp.2.1
  · change (cube 4 p.payload).length ≤ 16 * p.payload.length
    simpa only [show (2 : ℕ) ^ 4 = 16 from rfl, Nat.mul_comm] using length_cube p.payload hp.2.1

theorem semantics (boxed : Bool) (p : PolynomialData) (hp : StrictPositivityProblem.Domain p) :
    StrictPositivityProblem.Positive boxed p ↔ Positive boxed (data boxed p) := by
  cases boxed
  · exact (orthant_positive_iff p.payload).trans
      (orthant_relabel (finSumFinEquiv : Fin p.arity ⊕ Fin p.arity ≃ Fin (p.arity + p.arity)) (orthant p.payload))
  · exact cube_positive_iff p.payload hp.2.1

theorem decode_code (boxed : Bool) (p : PolynomialData) :
    decode (code boxed p) = some (data boxed p) := SparsePolynomialCodec.decode_code _

theorem coefficient_bound_bits : 530841600 < (2 : ℕ) ^ 29 := by decide

end JointThermoComplexity.Complexity.FinitePositiveCoordinates

#print axioms JointThermoComplexity.Complexity.FinitePositiveCoordinates.data
#print axioms JointThermoComplexity.Complexity.FinitePositiveCoordinates.data_domain
#print axioms JointThermoComplexity.Complexity.FinitePositiveCoordinates.length_bound
#print axioms JointThermoComplexity.Complexity.FinitePositiveCoordinates.semantics
