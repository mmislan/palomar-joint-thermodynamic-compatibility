module
public import proofs.JointThermoComplexity.Complexity.DenseCanonicalSource
public import proofs.JointThermoComplexity.Complexity.DenseTwoPass

set_option autoImplicit false
@[expose] public section

/-! Both complete actual branch words serialize the original reaction table,
including the two initial records and every stored normalization row. -/

namespace JointThermoComplexity.Complexity.DenseCanonicalBranch
open DenseCanonicalPacket

theorem index_self (N : ℕ) (i : Fin (N + 2)) : DensePacketControl.index N i.val = i := by
  apply Fin.ext
  exact DensePacketControl.index_val N i.val (by have h := i.isLt; omega)

theorem records_two (boxed right : Bool) (p : SparsePolynomialCodec.PolynomialData) :
    records boxed right p 0 2 =
      DenseRecordCore.recordWord right (RationalPolynomialNetwork.left boxed p) (RationalPolynomialNetwork.right boxed p)
        (DenseFixedComplexOriginal.initialVertex false p.payload.length) ++
      DenseRecordCore.recordWord right (RationalPolynomialNetwork.left boxed p) (RationalPolynomialNetwork.right boxed p)
        (DenseFixedComplexOriginal.initialVertex true p.payload.length) := by
  have h0 : DensePacketControl.index p.payload.length 0 = DenseFixedComplexOriginal.initialVertex false p.payload.length := by
    apply Fin.ext
    rw [DensePacketControl.index_val _ _ (by omega)]
    rfl
  have h1 : DensePacketControl.index p.payload.length 1 = DenseFixedComplexOriginal.initialVertex true p.payload.length := by
    apply Fin.ext
    rw [DensePacketControl.index_val _ _ (by omega)]
    rfl
  simp only [records, List.ofFn_succ, List.ofFn_zero, List.flatten_cons, List.flatten_nil,
    Fin.val_zero, Fin.val_succ, Nat.zero_add, h0, h1, List.append_nil]

theorem fixed_row (boxed right offset : Bool) (p : SparsePolynomialCodec.PolynomialData) :
    DenseFixedPacket.rowWord boxed right offset p.arity (FinitePositiveCoordinates.data boxed p).payload.length
      (RawOffsetBounds.offset (FinitePositiveCoordinates.data boxed p).payload) =
      DenseRecordCore.recordWord right (RationalPolynomialNetwork.left boxed (FinitePositiveCoordinates.data boxed p))
        (RationalPolynomialNetwork.right boxed (FinitePositiveCoordinates.data boxed p))
        (DenseFixedComplexOriginal.initialVertex offset (FinitePositiveCoordinates.data boxed p).payload.length) := by
  cases boxed with
  | false => exact DenseRecordWordIdentity.unboxed_fixed right offset _ _
  | true => exact DenseRecordWordIdentity.boxed_fixed right offset _

theorem fixed_packet (boxed right : Bool) (p : SparsePolynomialCodec.PolynomialData) :
    DenseFixedPacket.word boxed right p.arity (FinitePositiveCoordinates.data boxed p).payload.length
      (RawOffsetBounds.offset (FinitePositiveCoordinates.data boxed p).payload) =
      records boxed right (FinitePositiveCoordinates.data boxed p) 0 2 := by
  rw [DenseFixedPacket.word, fixed_row, fixed_row, records_two]

theorem branch_code (boxed right : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (hp : SparseInteger.DegreeLE 4 p.payload) :
    DenseTwoPass.branchWord boxed right (SparsePolynomialCodec.code p) =
      records boxed right (FinitePositiveCoordinates.data boxed p) 0
        ((FinitePositiveCoordinates.data boxed p).payload.length + 2) := by
  unfold DenseTwoPass.branchWord DenseBranchPass.word
  have hs := DenseCanonicalSource.canonical_runWords boxed right p hp
  rw [DenseCanonicalControl.total_code boxed p hp] at hs
  rw [DenseCanonicalControl.arity_code, DenseCanonicalControl.total_code boxed p hp,
    DenseCanonicalControl.offset_code boxed p hp, fixed_packet,
    hs]
  simpa only [Nat.zero_add, Nat.add_comm] using
    (records_add boxed right (FinitePositiveCoordinates.data boxed p) 0 2
      (FinitePositiveCoordinates.data boxed p).payload.length).symm

theorem records_function (boxed right : Bool) (p : SparsePolynomialCodec.PolynomialData) :
    records boxed right p 0 (p.payload.length + 2) =
      FiniteCodec.functionCode (DataCodec.reaction (RationalLiteralNetwork.speciesCount
        (RationalPolynomialNetwork.externalCount boxed p) p.payload.length p.payload.length))
        (fun i : Fin (p.payload.length + 2) =>
          RationalLiteralNetwork.reaction (RationalPolynomialNetwork.left boxed p) (RationalPolynomialNetwork.right boxed p)
            (DenseComplexOriginal.index right p.payload.length i)) := by
  simp only [records, Nat.zero_add, index_self, FiniteCodec.functionCode_eq_flatMap,
    DenseRecordCore.recordWord, List.flatMap_def, List.map_ofFn, Function.comp_def]

theorem reactions_code (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData) :
    FiniteCodec.functionCode (DataCodec.reaction (RationalLiteralNetwork.speciesCount
      (RationalPolynomialNetwork.externalCount boxed p) p.payload.length p.payload.length))
      (RationalPolynomialNetwork.network boxed p).reactions =
      records boxed false p 0 (p.payload.length + 2) ++ records boxed true p 0 (p.payload.length + 2) := by
  have hf : (RationalPolynomialNetwork.network boxed p).reactions =
      Fin.append
        (fun i => RationalLiteralNetwork.reaction (RationalPolynomialNetwork.left boxed p) (RationalPolynomialNetwork.right boxed p)
          (DenseComplexOriginal.index false p.payload.length i))
        (fun i => RationalLiteralNetwork.reaction (RationalPolynomialNetwork.left boxed p) (RationalPolynomialNetwork.right boxed p)
          (DenseComplexOriginal.index true p.payload.length i)) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; rw [Fin.append_left]; rfl
    · intro j; rw [Fin.append_right]; rfl
  simp only [RationalLiteralNetwork.reactionCount] at hf ⊢
  rw [hf, DenseBlockWords.code_append, records_function, records_function]

end JointThermoComplexity.Complexity.DenseCanonicalBranch

#print axioms JointThermoComplexity.Complexity.DenseCanonicalBranch.branch_code
#print axioms JointThermoComplexity.Complexity.DenseCanonicalBranch.reactions_code
