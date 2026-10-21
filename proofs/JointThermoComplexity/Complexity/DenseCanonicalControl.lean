module
public import proofs.JointThermoComplexity.Complexity.DenseRecordWordIdentity
public import proofs.JointThermoComplexity.Complexity.DenseTwoPassControl
public import proofs.JointThermoComplexity.Complexity.CountedSparseIdentity

set_option autoImplicit false
@[expose] public section

/-! The actual all-raw parser/count controls agree with the exact finite
normalization data on every canonically encoded degree-four source. -/

namespace JointThermoComplexity.Complexity.DenseCanonicalControl
open DenseTwoPassControl

theorem arity_code (p : SparsePolynomialCodec.PolynomialData) : arity (SparsePolynomialCodec.code p) = p.arity := SparseCountedEntry.count_code p

theorem total_code (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : SparseInteger.DegreeLE 4 p.payload) :
    total boxed (SparsePolynomialCodec.code p) = (FinitePositiveCoordinates.data boxed p).payload.length := by
  change (SparseDimensionEntry.outcome boxed (SparsePolynomialCodec.code p)).rows = _
  rw [SparseDimensionEntry.outcome_code boxed p hp]
  exact CountedSparseIdentity.rows_data boxed p

theorem offset_code (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : SparseInteger.DegreeLE 4 p.payload) :
    offset boxed (SparsePolynomialCodec.code p) = RawOffsetBounds.offset (FinitePositiveCoordinates.data boxed p).payload := by
  change (SparseDimensionEntry.outcome boxed (SparsePolynomialCodec.code p)).base.offset = _
  rw [SparseDimensionEntry.outcome_code boxed p hp]
  exact SparseOffsetIdentity.total_data boxed p

theorem initial_code (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : SparseInteger.DegreeLE 4 p.payload) :
    initial boxed (SparsePolynomialCodec.code p) =
      ⟨⟨true, RealSyntax.binderCode p.arity, SparseOffsetCode.code p.payload, RawOffsetBounds.offset (FinitePositiveCoordinates.data boxed p).payload⟩, 0⟩ := by
  unfold initial DenseReplayControl.state DenseReplayControl.rescan
  rw [SparseDimensionEntry.outcome_code boxed p hp]
  dsimp only [SparseDimensionRewind.restart]
  rw [SparseDenseRescan.outcome_code]
  rw [SparseOffsetIdentity.total_data]

theorem final_before_code (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : SparseInteger.DegreeLE 4 p.payload) :
    (finalState boxed (SparsePolynomialCodec.code p)).base.before = SparsePolynomialCodec.code p := by
  have h := DenseReplayControl.run_same boxed (SparsePolynomialCodec.code p).length _ _ (DenseReplayControl.state_same boxed (SparsePolynomialCodec.code p))
  have hb := h.2.1
  change (finalState boxed (SparsePolynomialCodec.code p)).base.before = (SparseDimensionEntry.outcome boxed (SparsePolynomialCodec.code p)).base.before at hb
  rw [SparseDimensionEntry.outcome_code boxed p hp] at hb
  exact hb

theorem final_input_code (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : SparseInteger.DegreeLE 4 p.payload) :
    (finalState boxed (SparsePolynomialCodec.code p)).base.input = [] := by
  have h := DenseReplayControl.run_same boxed (SparsePolynomialCodec.code p).length _ _ (DenseReplayControl.state_same boxed (SparsePolynomialCodec.code p))
  have hi := h.2.2.1
  change (finalState boxed (SparsePolynomialCodec.code p)).base.input = (SparseDimensionEntry.outcome boxed (SparsePolynomialCodec.code p)).base.input at hi
  rw [SparseDimensionEntry.outcome_code boxed p hp] at hi
  exact hi

theorem final_stopped_code (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) (hp : SparseInteger.DegreeLE 4 p.payload) :
    (finalState boxed (SparsePolynomialCodec.code p)).base.running = false := by
  have h := DenseReplayControl.run_same boxed (SparsePolynomialCodec.code p).length _ _ (DenseReplayControl.state_same boxed (SparsePolynomialCodec.code p))
  have hr := h.1
  change (finalState boxed (SparsePolynomialCodec.code p)).base.running = (SparseDimensionEntry.outcome boxed (SparsePolynomialCodec.code p)).base.running at hr
  rw [SparseDimensionEntry.outcome_code boxed p hp] at hr
  exact hr

theorem external_count (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) :
    RationalPolynomialNetwork.externalCount boxed (FinitePositiveCoordinates.data boxed p) = DenseDimensionProgram.external boxed p.arity := by
  cases boxed with
  | false => change p.arity + p.arity + 1 = 2 * p.arity + 1; omega
  | true => rfl

theorem species_count (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) :
    RationalLiteralNetwork.speciesCount (RationalPolynomialNetwork.externalCount boxed (FinitePositiveCoordinates.data boxed p))
      (FinitePositiveCoordinates.data boxed p).payload.length (FinitePositiveCoordinates.data boxed p).payload.length =
        SparseDimensionWords.species boxed p.arity (FinitePositiveCoordinates.data boxed p).payload.length := by
  rw [external_count]
  unfold RationalLiteralNetwork.speciesCount SparseDimensionWords.species DenseDimensionProgram.external
  cases boxed <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem reaction_count (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) :
    RationalLiteralNetwork.reactionCount (FinitePositiveCoordinates.data boxed p).payload.length (FinitePositiveCoordinates.data boxed p).payload.length =
      SparseDimensionWords.reactions (FinitePositiveCoordinates.data boxed p).payload.length := by
  unfold RationalLiteralNetwork.reactionCount SparseDimensionWords.reactions
  omega

theorem header_code (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) :
    SparseDimensionWords.header boxed p.arity (FinitePositiveCoordinates.data boxed p).payload.length =
      RealSyntax.binderCode (RationalLiteralNetwork.speciesCount (RationalPolynomialNetwork.externalCount boxed (FinitePositiveCoordinates.data boxed p))
        (FinitePositiveCoordinates.data boxed p).payload.length (FinitePositiveCoordinates.data boxed p).payload.length) ++
      RealSyntax.binderCode (RationalLiteralNetwork.reactionCount (FinitePositiveCoordinates.data boxed p).payload.length (FinitePositiveCoordinates.data boxed p).payload.length) ++
      RealSyntax.binderCode 2 := by
  rw [species_count, reaction_count]
  rfl

end JointThermoComplexity.Complexity.DenseCanonicalControl

#print axioms JointThermoComplexity.Complexity.DenseCanonicalControl.initial_code
#print axioms JointThermoComplexity.Complexity.DenseCanonicalControl.header_code
