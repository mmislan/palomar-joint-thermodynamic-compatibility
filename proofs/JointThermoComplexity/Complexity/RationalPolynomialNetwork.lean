module
public import proofs.JointThermoComplexity.Complexity.RationalPolynomialBranches
public import proofs.JointThermoComplexity.Complexity.RationalBranchRelabel
public import proofs.JointThermoComplexity.Complexity.RationalLiteralFeasibility
public import proofs.JointThermoComplexity.Complexity.FinitePositiveCoordinates
public import proofs.JointThermoComplexity.OpenCubeReduction

set_option autoImplicit false
@[expose] public section

/-! Concrete finite rational networks for raw polynomial positivity, including
the extra unboxed offset coordinate and exact fixed factor restrictions. -/

namespace JointThermoComplexity.Complexity.RationalPolynomialNetwork
open SparsePolynomialCodec RationalBranchData RawChemicalPolynomial

abbrev externalCount (boxed : Bool) (p : PolynomialData) : ℕ := if boxed then p.arity else p.arity + 1

def left : (boxed : Bool) → (p : PolynomialData) → Data (Fin (externalCount boxed p)) p.payload.length
  | false, p => RationalBranchRelabel.relabel (finSuccEquiv p.arity).symm
      (RationalPolynomialBranches.unboxedLeft p.payload)
  | true, p => RationalPolynomialBranches.boxedLeft p.payload

def right : (boxed : Bool) → (p : PolynomialData) → Data (Fin (externalCount boxed p)) p.payload.length
  | false, p => RationalBranchRelabel.relabel (finSuccEquiv p.arity).symm
      (RationalPolynomialBranches.unboxedRight p.payload)
  | true, p => RationalPolynomialBranches.boxedRight p.payload

def network (boxed : Bool) (p : PolynomialData) := RationalLiteralNetwork.network boxed (left boxed p) (right boxed p)
def input (boxed : Bool) (p : PolynomialData) := RationalLiteralNetwork.input boxed (left boxed p) (right boxed p)
def code (boxed : Bool) (p : PolynomialData) : List Bool := (input boxed p).code

theorem decode_code (boxed : Bool) (p : PolynomialData) :
    NetworkCodec.decode (code boxed p) = some (input boxed p) := NetworkCodec.decode_code _

theorem semantics (boxed : Bool) (p : PolynomialData) :
    (network boxed p).Feasible ↔ FinitePositiveCoordinates.Positive boxed p := by
  cases boxed
  · change (RationalLiteralNetwork.network false _ _).Feasible ↔ SparsePositiveCoordinates.PositiveOrthant p.payload
    rw [RationalLiteralFeasibility.unboxed_iff]
    simp only [left, right]
    rw [RationalBranchRelabel.multicac_relabel,
      RationalPolynomialBranches.unboxedLeft_eq, RationalPolynomialBranches.unboxedRight_eq,
      Emitted.source_unboxed_reduction]
    simp only [SparsePositiveCoordinates.PositiveOrthant, polynomial_eval]
  · change (RationalLiteralNetwork.network true _ _).Feasible ↔ SparsePositiveCoordinates.PositiveBox p.payload
    rw [RationalLiteralFeasibility.boxed_iff]
    simp only [left, right]
    rw [RationalPolynomialBranches.boxedLeft_eq,
      RationalPolynomialBranches.boxedRight_eq]
    simpa [externalCount, SparsePositiveCoordinates.PositiveBox, polynomial_eval] using
      (Emitted.boxed_open_reduction (coefficients p.payload) (exponents p.payload)).2.2.symm

theorem normalized_semantics (boxed : Bool) (p : PolynomialData) (hp : StrictPositivityProblem.Domain p) :
    (network boxed (FinitePositiveCoordinates.data boxed p)).Feasible ↔ StrictPositivityProblem.Positive boxed p :=
  (semantics boxed _).trans (FinitePositiveCoordinates.semantics boxed p hp).symm

theorem supplied_PACs (boxed : Bool) (p : PolynomialData) :
    ∀ a : Fin 2, (LiteralBridge.toMotif (network boxed p) a).IsPAC :=
  RationalLiteralIdentity.supplied_PACs boxed _ _

theorem left_numerator (boxed : Bool) (p : PolynomialData) (i : Fin (p.payload.length + 1)) :
    (left boxed p).numerator i ≤ 2 := by
  cases boxed <;> change (1 : ℕ) ≤ 2 <;> decide

theorem right_numerator (boxed : Bool) (p : PolynomialData) (i : Fin (p.payload.length + 1)) :
    (right boxed p).numerator i ≤ 2 := by
  cases boxed <;> change (2 : ℕ) ≤ 2 <;> decide

theorem factor_bounds (boxed : Bool) (p : PolynomialData)
    (r : Fin (RationalLiteralNetwork.reactionCount p.payload.length p.payload.length)) :
    0 < (((network boxed p).reactions r).numerator : ℝ) / ((network boxed p).reactions r).denominator ∧
      (((network boxed p).reactions r).numerator : ℝ) / ((network boxed p).reactions r).denominator ≤ 2 := by
  obtain ⟨r, rfl⟩ := (RationalLiteralNetwork.reactionNumbering p.payload.length p.payload.length).surjective r
  cases r with
  | inl i =>
    simpa only [network, RationalLiteralNetwork.network, RationalLiteralNetwork.reaction,
      Equiv.symm_apply_apply, RationalLiteralNetwork.numeratorRaw, RationalLiteralNetwork.denominatorRaw, Sum.elim_inl]
      using (left boxed p).factor_bounds (left_numerator boxed p) i
  | inr i =>
    simpa only [network, RationalLiteralNetwork.network, RationalLiteralNetwork.reaction,
      Equiv.symm_apply_apply, RationalLiteralNetwork.numeratorRaw, RationalLiteralNetwork.denominatorRaw, Sum.elim_inr]
      using (right boxed p).factor_bounds (right_numerator boxed p) i

end JointThermoComplexity.Complexity.RationalPolynomialNetwork

#print axioms JointThermoComplexity.Complexity.RationalPolynomialNetwork.code
#print axioms JointThermoComplexity.Complexity.RationalPolynomialNetwork.decode_code
#print axioms JointThermoComplexity.Complexity.RationalPolynomialNetwork.semantics
#print axioms JointThermoComplexity.Complexity.RationalPolynomialNetwork.normalized_semantics
#print axioms JointThermoComplexity.Complexity.RationalPolynomialNetwork.supplied_PACs
#print axioms JointThermoComplexity.Complexity.RationalPolynomialNetwork.factor_bounds
