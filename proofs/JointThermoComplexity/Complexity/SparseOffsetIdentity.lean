module
public import proofs.JointThermoComplexity.Complexity.SparseOffsetCode
public import proofs.JointThermoComplexity.Complexity.RawOffsetBounds
public import proofs.JointThermoComplexity.Complexity.FinitePositiveCoordinates

set_option autoImplicit false
@[expose] public section

/-! The actual offset pass computes the exact input-fixed chemical offset. -/

namespace JointThermoComplexity.Complexity.SparseOffsetIdentity
open SparseInteger SparsePolynomialCodec
open scoped BigOperators
variable {V : Type}

theorem rawSum_eq (p : Poly V) : OffsetTemplateData.rawSum p =
    ∑ i : Fin p.length, RationalBranchCoefficients.rightDenominator (RawChemicalPolynomial.coefficientInteger p i) *
      2 ^ p[i].2.length := by
  symm
  simpa only [List.sum_ofFn, Fin.getElem_fin, RawChemicalPolynomial.coefficientInteger, OffsetTemplateData.rawSum]
    using congrArg List.sum (List.ofFn_getElem_eq_map p
      (fun a => RationalBranchCoefficients.rightDenominator a.1 * 2 ^ a.2.length))

theorem offset_eq (p : Poly V) : 1 + OffsetTemplateData.rawSum p = RawOffsetBounds.offset p := by
  rw [rawSum_eq]
  rfl

theorem total_data (boxed : Bool) (p : PolynomialData) :
    1 + SparseOffsetCode.total boxed p.payload = RawOffsetBounds.offset (FinitePositiveCoordinates.data boxed p).payload := by
  cases boxed with
  | false =>
    change 1 + SparseOffsetCode.total false p.payload =
      RawOffsetBounds.offset (relabel finSumFinEquiv (SparseSubstitution.orthant p.payload))
    rw [← offset_eq, SparseOffsetCode.total_orthant, SparseOffsetCode.rawSum_relabel]
  | true =>
    change 1 + SparseOffsetCode.total true p.payload = RawOffsetBounds.offset (SparseSubstitution.cube 4 p.payload)
    rw [SparseOffsetCode.total_cube, offset_eq]

theorem hoareTime (boxed : Bool) (p : PolynomialData) (hp : DegreeLE 4 p.payload)
    (L : ℕ) (before suffix emitted : List Bool)
    (hlen : (SparseOffsetCode.code p.payload ++ suffix).length ≤ L)
    (R : (Fin 32 → _root_.Complexity.Tape) → Prop) (hR : SparseOffsetLoop.Stable R) :
    (SparseOffsetLoop.machine boxed).HoareTime
      (fun inp work out => SparseOffsetMarkedStep.Inv L emitted R
        ⟨true, before, SparseOffsetCode.code p.payload ++ suffix, 1⟩ inp work out ∧
          _root_.Complexity.TM.IsReg L (work SparseOffsetPorts.fuel.castSucc))
      (fun inp work out => SparseOffsetMarkedStep.Inv L emitted R
        ⟨false, before ++ SparseOffsetCode.code p.payload, suffix,
          RawOffsetBounds.offset (FinitePositiveCoordinates.data boxed p).payload⟩ inp work out ∧
          _root_.Complexity.TM.IsReg L (work SparseOffsetPorts.fuel.castSucc))
      (3328 * L ^ 3 + 8687019 * L ^ 2 + 10897192 * L + 2) := by
  have ht := SparseOffsetCode.hoareTime boxed p.payload hp L 1 1 before suffix emitted hlen (by decide) R hR
  rw [total_data boxed p, SparseOffsetLoop.cubic_timeBound] at ht
  exact ht

end JointThermoComplexity.Complexity.SparseOffsetIdentity

#print axioms JointThermoComplexity.Complexity.SparseOffsetIdentity.rawSum_eq
#print axioms JointThermoComplexity.Complexity.SparseOffsetIdentity.total_data
#print axioms JointThermoComplexity.Complexity.SparseOffsetIdentity.hoareTime
