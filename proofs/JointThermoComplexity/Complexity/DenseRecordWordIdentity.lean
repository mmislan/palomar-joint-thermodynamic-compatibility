module
public import proofs.JointThermoComplexity.Complexity.DenseFixedRawRecord

set_option autoImplicit false
@[expose] public section

/-! Raw record words agree with the original reaction codec once their exact
coefficient and external power data have been identified. -/

namespace JointThermoComplexity.Complexity.DenseRecordWordIdentity
open DenseComplexOriginal

theorem fixed (boxed right offset : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (gamma : Fin (RationalPolynomialNetwork.externalCount boxed p) → ℕ)
    (hg : gamma = DenseComplexOriginal.gamma right (RationalPolynomialNetwork.left boxed p) (RationalPolynomialNetwork.right boxed p)
      (DenseFixedComplexOriginal.initialVertex offset p.payload.length)) :
    DenseFixedRawRecord.word boxed right offset (RawOffsetBounds.offset p.payload) p.payload.length
      (DenseFixedComplexOriginal.initialVertex offset p.payload.length) (RationalPolynomialNetwork.externalCount boxed p) gamma =
      DenseRecordCore.recordWord right (RationalPolynomialNetwork.left boxed p) (RationalPolynomialNetwork.right boxed p)
        (DenseFixedComplexOriginal.initialVertex offset p.payload.length) := by
  unfold DenseRecordCore.recordWord
  rw [DenseFactorCode.record_code, DenseComplexOriginal.vector_eq right false, DenseComplexOriginal.vector_eq right true,
    DenseFactorCode.fixed_code, ← hg]
  rfl

theorem boxed_fixed (right offset : Bool) (p : SparsePolynomialCodec.PolynomialData) :
    DenseFixedRawRecord.word true right offset (RawOffsetBounds.offset p.payload) p.payload.length
      (DenseFixedComplexOriginal.initialVertex offset p.payload.length) p.arity (fun _ => 0) =
      DenseRecordCore.recordWord right (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p)
        (DenseFixedComplexOriginal.initialVertex offset p.payload.length) :=
  fixed true right offset p (fun _ => 0) (DenseFixedComplexOriginal.boxed_gamma right offset p).symm

theorem unboxed_fixed (right offset : Bool) (n : ℕ) (payload : SparseInteger.Poly (Fin (n + n))) :
    DenseFixedRawRecord.word false right offset (RawOffsetBounds.offset payload) payload.length
      (DenseFixedComplexOriginal.initialVertex offset payload.length) ((n + n) + 1)
      (Fin.cons (DenseFixedComplexOriginal.offsetPower offset) (fun _ => 0)) =
      DenseRecordCore.recordWord right (RationalPolynomialNetwork.left false ⟨n + n, payload⟩) (RationalPolynomialNetwork.right false ⟨n + n, payload⟩)
        (DenseFixedComplexOriginal.initialVertex offset payload.length) :=
  fixed false right offset ⟨n + n, payload⟩ _ (DenseFixedComplexOriginal.unboxed_gamma right offset payload).symm

theorem regular (boxed right : Bool) (p : SparsePolynomialCodec.PolynomialData) (j : Fin p.payload.length)
    (gamma : Fin (RationalPolynomialNetwork.externalCount boxed p) → ℕ) (t : ℤ) (v : ℕ) (negative : Bool)
    (hg : gamma = DenseComplexOriginal.gamma right (RationalPolynomialNetwork.left boxed p) (RationalPolynomialNetwork.right boxed p) j.succ.succ)
    (hc : RawChemicalPolynomial.coefficientInteger p.payload j = RationalFactorWords.coefficient negative v * t) :
    DenseRawRecord.word right p.payload.length j.succ.succ (RationalPolynomialNetwork.externalCount boxed p) gamma t v negative =
      DenseRecordCore.recordWord right (RationalPolynomialNetwork.left boxed p) (RationalPolynomialNetwork.right boxed p) j.succ.succ := by
  unfold DenseRecordCore.recordWord
  rw [DenseFactorCode.record_code, DenseComplexOriginal.vector_eq right false, DenseComplexOriginal.vector_eq right true,
    DenseFactorCode.regular_code, hc, ← hg]
  rfl

end JointThermoComplexity.Complexity.DenseRecordWordIdentity

#print axioms JointThermoComplexity.Complexity.DenseRecordWordIdentity.fixed
#print axioms JointThermoComplexity.Complexity.DenseRecordWordIdentity.regular
