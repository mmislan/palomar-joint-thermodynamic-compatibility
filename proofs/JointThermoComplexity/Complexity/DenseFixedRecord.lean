module
public import proofs.JointThermoComplexity.Complexity.DenseRegularRecord

set_option autoImplicit false
@[expose] public section

/-! Complete baseline and offset reaction records on both sides, including the
zero-payload offset/last-row case. -/

namespace JointThermoComplexity.Complexity.DenseFixedRecord
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseRecordCore DenseRecordFrame DenseComplexOriginal DenseFixedComplexOriginal
variable {n : ℕ}

def Source (U : ℕ) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop := Register U (work 13) ∧ R work
theorem source_stable (product : Bool) (U : ℕ) (R : (Fin 64 → Tape) → Prop)
    (hR : DenseComplexPorts.Stable product R) : DenseComplexPorts.Stable product (Source U R) := by
  rintro work next he ⟨hu, hr⟩
  have h13 : DenseComplexPorts.Outside product 13 := by
    cases product <;> unfold DenseComplexPorts.Outside DenseComplexPorts.target <;> decide
  exact ⟨by rw [he 13 h13]; exact hu, hR work next he hr⟩

theorem factor_hoareTime (boxed right offset : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (B : ℕ) (hB : (RawOffsetBounds.offset p.payload).bits.length ≤ B) (n : ℕ)
    (R : (Fin 64 → Tape) → Prop) (before input emitted : List Bool) :
    (DenseFixedFactor.machine boxed right offset).HoareTime
      (Pre 0 (by decide) (fun _ => 0) n p.payload.length (initialVertex offset p.payload.length)
        before input emitted (Source (RawOffsetBounds.offset p.payload) R))
      (Pre 0 (by decide) (fun _ => 0) n p.payload.length (initialVertex offset p.payload.length) before input
        (emitted ++ DenseFactorCode.factor right (RationalPolynomialNetwork.left boxed p)
          (RationalPolynomialNetwork.right boxed p) (initialVertex offset p.payload.length))
        (Source (RawOffsetBounds.offset p.payload) R)) (3 * B + 11) := by
  have hh := DenseFixedFactor.original_hoareTime boxed right offset p B hB before input emitted
    (Fields 0 (by decide) (fun _ => 0) n p.payload.length (initialVertex offset p.payload.length) R)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hi, hn, hf, hz, hh, hN, hb, href, ha, hu, hr⟩
    exact ⟨hc, hs, hu, hi, hn, hf, hz, hh, hN, hb, href, ha, hr⟩
  · rintro inp work out ⟨hc, hs, hu, hi, hn, hf, hz, hh, hN, hb, href, ha, hr⟩
    exact ⟨hc, hs, hi, hn, hf, hz, hh, hN, hb, href, ha, hu, hr⟩
  · exact le_rfl

def machine (boxed right offset : Bool) (external : TM 64) : TM 64 :=
  DenseRecordCore.machine (DenseComplexCore.machine right false 1 external)
    (DenseProductBranch.machine right external) (DenseFixedFactor.machine boxed right offset)
def timeBound (right : Bool) (N B E : ℕ) : ℕ :=
  DenseComplexCore.bound right N B 1 E + DenseProductBranch.timeBound right N B E + (3 * B + 11) + 2

theorem boxed_hoareTime (right offset : Bool) (p : SparsePolynomialCodec.PolynomialData) (B : ℕ)
    (hU : (RawOffsetBounds.offset p.payload).bits.length ≤ B)
    (hI : (initialVertex offset p.payload.length).val.bits.length ≤ B)
    (hM : (vertex true (initialVertex offset p.payload.length)).val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop)
    (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R) :
    (machine true right offset DenseFixedExternalPower.boxedMachine).HoareTime
      (Pre 0 (by decide) (fun _ => 0) p.arity p.payload.length (initialVertex offset p.payload.length)
        before input emitted (Source (RawOffsetBounds.offset p.payload) R))
      (Pre 0 (by decide) (fun _ => 0) p.arity p.payload.length (initialVertex offset p.payload.length) before input
        (emitted ++ recordWord right (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p)
          (initialVertex offset p.payload.length)) (Source (RawOffsetBounds.offset p.payload) R))
      (timeBound right p.payload.length B (DenseFixedExternalPower.boxedBound p.arity)) := by
  apply DenseRecordCore.hoareTime _ _ _ right _ _ (initialVertex offset p.payload.length) 0 (by decide) (fun _ => 0) p.arity
    (DenseComplexCore.bound right p.payload.length B 1 (DenseFixedExternalPower.boxedBound p.arity))
    (DenseProductBranch.timeBound right p.payload.length B (DenseFixedExternalPower.boxedBound p.arity)) (3 * B + 11)
    ?_ ?_ (Source (RawOffsetBounds.offset p.payload) R)
    (source_stable false _ R hRa) (source_stable true _ R hRp)
    (factor_hoareTime true right offset p B hU p.arity R)
  · intro before input emitted S hS
    exact DenseFixedComplexOriginal.boxed_hoareTime right false offset p B 1 rfl hI before input emitted S hS
  · intro before input emitted S hS
    exact DenseProductEmit.fixed_boxed_hoareTime right offset p B hM before input emitted S hS

theorem unboxed_hoareTime (right offset : Bool) (payload : SparseInteger.Poly (Fin (n + n))) (B : ℕ)
    (hU : (RawOffsetBounds.offset payload).bits.length ≤ B)
    (hI : (initialVertex offset payload.length).val.bits.length ≤ B)
    (hM : (vertex true (initialVertex offset payload.length)).val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop)
    (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R) :
    (machine false right offset (DenseFixedExternalPower.unboxedMachine (offsetPower offset))).HoareTime
      (Pre 0 (by decide) (fun _ => 0) n payload.length (initialVertex offset payload.length)
        before input emitted (Source (RawOffsetBounds.offset payload) R))
      (Pre 0 (by decide) (fun _ => 0) n payload.length (initialVertex offset payload.length) before input
        (emitted ++ recordWord right (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
          (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) (initialVertex offset payload.length))
        (Source (RawOffsetBounds.offset payload) R))
      (timeBound right payload.length B (DenseFixedExternalPower.unboxedBound n (offsetPower offset))) := by
  apply DenseRecordCore.hoareTime _ _ _ right _ _ (initialVertex offset payload.length) 0 (by decide) (fun _ => 0) n
    (DenseComplexCore.bound right payload.length B 1 (DenseFixedExternalPower.unboxedBound n (offsetPower offset)))
    (DenseProductBranch.timeBound right payload.length B (DenseFixedExternalPower.unboxedBound n (offsetPower offset))) (3 * B + 11)
    ?_ ?_ (Source (RawOffsetBounds.offset payload) R)
    (source_stable false _ R hRa) (source_stable true _ R hRp)
    (factor_hoareTime false right offset ⟨n + n, payload⟩ B hU n R)
  · intro before input emitted S hS
    exact DenseFixedComplexOriginal.unboxed_hoareTime right false offset payload B 1 rfl hI before input emitted S hS
  · intro before input emitted S hS
    exact DenseProductEmit.fixed_unboxed_hoareTime right offset payload B hM before input emitted S hS

end JointThermoComplexity.Complexity.DenseFixedRecord

#print axioms JointThermoComplexity.Complexity.DenseFixedRecord.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseFixedRecord.unboxed_hoareTime
