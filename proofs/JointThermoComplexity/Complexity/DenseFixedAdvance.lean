module
public import proofs.JointThermoComplexity.Complexity.DenseRegularAdvance

set_option autoImplicit false
@[expose] public section

/-! Actual complete records followed by a retained binary current-index increment. -/

namespace JointThermoComplexity.Complexity.DenseFixedAdvance
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseRecordCore DenseRecordFrame DenseComplexOriginal DenseFixedComplexOriginal DenseFixedRecord
variable {n : ℕ}

theorem source_increment (U : ℕ) (R : (Fin 64 → Tape) → Prop)
    (hR : BinaryIncrementFramed.Stable (38 : Fin 64) R) :
    BinaryIncrementFramed.Stable (38 : Fin 64) (Source U R) := by
  rintro work next he ⟨hu, hr⟩
  exact ⟨by rw [he 13 (by decide)]; exact hu, hR work next he hr⟩

theorem boxed_hoareTime (right offset : Bool) (p : SparsePolynomialCodec.PolynomialData) (B : ℕ)
    (hU : (RawOffsetBounds.offset p.payload).bits.length ≤ B)
    (hI : (initialVertex offset p.payload.length).val.bits.length ≤ B)
    (hM : (vertex true (initialVertex offset p.payload.length)).val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop)
    (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R)
    (hRi : BinaryIncrementFramed.Stable (38 : Fin 64) R) :
    (DenseRecordAdvance.machine (DenseFixedRecord.machine true right offset DenseFixedExternalPower.boxedMachine)).HoareTime
      (Pre 0 (by decide) (fun _ => 0) p.arity p.payload.length (initialVertex offset p.payload.length)
        before input emitted (Source (RawOffsetBounds.offset p.payload) R))
      (DenseRecordAdvance.At ((initialVertex offset p.payload.length).val + 1) 0 (by decide) (fun _ => 0) p.arity p.payload.length (initialVertex offset p.payload.length) before input
        (emitted ++ recordWord right (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p)
          (initialVertex offset p.payload.length)) (Source (RawOffsetBounds.offset p.payload) R))
      (timeBound right p.payload.length B (DenseFixedExternalPower.boxedBound p.arity) + 2 * B + 5) := by
  apply DenseRecordAdvance.hoareTime _ right _ _ (initialVertex offset p.payload.length) 0 (by decide) (fun _ => 0) p.arity B
    (timeBound right p.payload.length B (DenseFixedExternalPower.boxedBound p.arity)) hI (Source (RawOffsetBounds.offset p.payload) R)
    (source_increment _ R hRi)
  intro before input emitted
  exact DenseFixedRecord.boxed_hoareTime right offset p B hU hI hM before input emitted R hRa hRp

theorem unboxed_hoareTime (right offset : Bool) (payload : SparseInteger.Poly (Fin (n + n))) (B : ℕ)
    (hU : (RawOffsetBounds.offset payload).bits.length ≤ B)
    (hI : (initialVertex offset payload.length).val.bits.length ≤ B)
    (hM : (vertex true (initialVertex offset payload.length)).val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop)
    (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R)
    (hRi : BinaryIncrementFramed.Stable (38 : Fin 64) R) :
    (DenseRecordAdvance.machine (DenseFixedRecord.machine false right offset (DenseFixedExternalPower.unboxedMachine (offsetPower offset)))).HoareTime
      (Pre 0 (by decide) (fun _ => 0) n payload.length (initialVertex offset payload.length)
        before input emitted (Source (RawOffsetBounds.offset payload) R))
      (DenseRecordAdvance.At ((initialVertex offset payload.length).val + 1) 0 (by decide) (fun _ => 0) n payload.length (initialVertex offset payload.length) before input
        (emitted ++ recordWord right (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
          (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) (initialVertex offset payload.length))
        (Source (RawOffsetBounds.offset payload) R))
      (timeBound right payload.length B (DenseFixedExternalPower.unboxedBound n (offsetPower offset)) + 2 * B + 5) := by
  apply DenseRecordAdvance.hoareTime _ right _ _ (initialVertex offset payload.length) 0 (by decide) (fun _ => 0) n B
    (timeBound right payload.length B (DenseFixedExternalPower.unboxedBound n (offsetPower offset))) hI (Source (RawOffsetBounds.offset payload) R)
    (source_increment _ R hRi)
  intro before input emitted
  exact DenseFixedRecord.unboxed_hoareTime right offset payload B hU hI hM before input emitted R hRa hRp

end JointThermoComplexity.Complexity.DenseFixedAdvance

#print axioms JointThermoComplexity.Complexity.DenseFixedAdvance.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseFixedAdvance.unboxed_hoareTime
