module
public import proofs.JointThermoComplexity.Complexity.CountedSparseCode
public import proofs.JointThermoComplexity.Complexity.SparseOffsetIdentity

set_option autoImplicit false
@[expose] public section

/-! The actual counted pass returns the exact chemical offset and term count. -/

namespace JointThermoComplexity.Complexity.CountedSparseIdentity
open SparseInteger SparsePolynomialCodec

theorem rows_data (boxed : Bool) (p : PolynomialData) :
    CountedSparseCode.rowTotal p.payload = (FinitePositiveCoordinates.data boxed p).payload.length := by
  cases boxed with
  | false =>
    change CountedSparseCode.rowTotal p.payload =
      (relabel finSumFinEquiv (SparseSubstitution.orthant p.payload)).length
    rw [length_relabel, CountedSparseCode.orthant_length]
  | true => exact (CountedSparseCode.cube_length 4 p.payload).symm

theorem hoareTime (boxed : Bool) (p : PolynomialData) (hp : DegreeLE 4 p.payload)
    (L : ℕ) (before suffix emitted : List Bool)
    (hlen : (SparseOffsetCode.code p.payload ++ suffix).length ≤ L)
    (R : (Fin 32 → _root_.Complexity.Tape) → Prop) (hR : CountedSparseLoop.Stable R) :
    (CountedSparseLoop.machine boxed).HoareTime
      (fun inp work out => CountedMarkedStep.Inv L emitted R
        ⟨⟨true, before, SparseOffsetCode.code p.payload ++ suffix, 1⟩, 0⟩ inp work out ∧
          _root_.Complexity.TM.IsReg L (work SparseOffsetPorts.fuel.castSucc))
      (fun inp work out => CountedMarkedStep.Inv L emitted R
        ⟨⟨false, before ++ SparseOffsetCode.code p.payload, suffix,
          RawOffsetBounds.offset (FinitePositiveCoordinates.data boxed p).payload⟩,
            (FinitePositiveCoordinates.data boxed p).payload.length⟩ inp work out ∧
          _root_.Complexity.TM.IsReg L (work SparseOffsetPorts.fuel.castSucc))
      (3328 * L ^ 3 + 8687531 * L ^ 2 + 10897792 * L + 2) := by
  have ht := CountedSparseCode.hoareTime boxed p.payload hp L 1 0 1 0 before suffix emitted hlen (by decide) (by decide) R hR
  rw [SparseOffsetIdentity.total_data boxed p, Nat.zero_add, rows_data boxed p, CountedSparseLoop.cubic_timeBound] at ht
  exact ht

end JointThermoComplexity.Complexity.CountedSparseIdentity

#print axioms JointThermoComplexity.Complexity.CountedSparseIdentity.rows_data
#print axioms JointThermoComplexity.Complexity.CountedSparseIdentity.hoareTime
