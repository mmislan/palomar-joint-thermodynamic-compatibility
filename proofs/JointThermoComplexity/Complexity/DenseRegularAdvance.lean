module
public import proofs.JointThermoComplexity.Complexity.DenseRecordAdvance

set_option autoImplicit false
@[expose] public section

/-! Actual complete records followed by a retained binary current-index increment. -/

namespace JointThermoComplexity.Complexity.DenseRegularAdvance
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseRecordCore DenseRecordFrame DenseComplexOriginal DenseRegularRecord
variable {n : ℕ}

theorem source_increment (v : ℕ) (negative : Bool) (R : (Fin 64 → Tape) → Prop)
    (hR : BinaryIncrementFramed.Stable (38 : Fin 64) R) :
    BinaryIncrementFramed.Stable (38 : Fin 64) (Source v negative R) := by
  rintro work next he ⟨hv, hn, ha, hb, hz, hr⟩
  exact ⟨by rw [he 0 (by decide)]; exact hv, by rw [he 1 (by decide)]; exact hn,
    by rw [he 12 (by decide)]; exact ha, by rw [he 63 (by decide)]; exact hb,
    by rw [he 63 (by decide)]; exact hz, hR work next he hr⟩

theorem boxed_hoareTime (right : Bool) (p : SparsePolynomialCodec.PolynomialData) (j : Fin p.payload.length)
    (vs : List (Fin p.arity)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length)) (hocc : occ.length ≤ 4)
    (hrow : p.payload[j.val].2 = occ.map (RawNormalizationTemplates.lookup vs))
    (t : ℤ) (v B : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (hcoef : RawChemicalPolynomial.coefficientInteger p.payload j = RationalFactorWords.coefficient negative v * t)
    (hI : j.succ.succ.val.bits.length ≤ B) (hM : (vertex true j.succ.succ).val.bits.length ≤ B)
    (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop)
    (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R) (hRf : DenseFactorFrame.Stable R)
    (hRi : BinaryIncrementFramed.Stable (38 : Fin 64) R) :
    (DenseRecordAdvance.machine (DenseRegularRecord.machine right (DenseExternalPower.boxedMachine vs.length hcap occ) t)).HoareTime
      (Pre vs.length hcap (DensePowerReady.values vs) p.arity p.payload.length j.succ.succ before input emitted (Source v negative R))
      (DenseRecordAdvance.At (j.succ.succ.val + 1) vs.length hcap (DensePowerReady.values vs) p.arity p.payload.length j.succ.succ before input
        (emitted ++ recordWord right (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p) j.succ.succ)
        (Source v negative R)) (timeBound right p.payload.length B (DenseExternalPower.vectorBound p.arity B) + 2 * B + 5) := by
  apply DenseRecordAdvance.hoareTime _ right _ _ j.succ.succ vs.length hcap (DensePowerReady.values vs) p.arity B
    (timeBound right p.payload.length B (DenseExternalPower.vectorBound p.arity B)) hI (Source v negative R) (source_increment v negative R hRi)
  intro before input emitted
  exact DenseRegularRecord.boxed_hoareTime right p j vs hcap occ hocc hrow t v B negative hB ht hcoef hI hM hbits
    before input emitted R hRa hRp hRf

theorem unboxed_hoareTime (right : Bool) (payload : SparseInteger.Poly (Fin (n + n))) (j : Fin payload.length)
    (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length ⊕ Fin vs.length)) (hocc : occ.length ≤ 4)
    (hrow : payload[j.val].2 = DenseTemplatePowerCode.signedMonomial vs occ)
    (t : ℤ) (v B : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (hcoef : RawChemicalPolynomial.coefficientInteger payload j = RationalFactorWords.coefficient negative v * t)
    (hI : j.succ.succ.val.bits.length ≤ B) (hM : (vertex true j.succ.succ).val.bits.length ≤ B)
    (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop)
    (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R) (hRf : DenseFactorFrame.Stable R)
    (hRi : BinaryIncrementFramed.Stable (38 : Fin 64) R) :
    (DenseRecordAdvance.machine (DenseRegularRecord.machine right (DenseExternalPower.unboxedMachine vs.length hcap occ) t)).HoareTime
      (Pre vs.length hcap (DensePowerReady.values vs) n payload.length j.succ.succ before input emitted (Source v negative R))
      (DenseRecordAdvance.At (j.succ.succ.val + 1) vs.length hcap (DensePowerReady.values vs) n payload.length j.succ.succ before input
        (emitted ++ recordWord right (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
          (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) j.succ.succ) (Source v negative R))
      (timeBound right payload.length B (DenseExternalPower.unboxedBound n B) + 2 * B + 5) := by
  apply DenseRecordAdvance.hoareTime _ right _ _ j.succ.succ vs.length hcap (DensePowerReady.values vs) n B
    (timeBound right payload.length B (DenseExternalPower.unboxedBound n B)) hI (Source v negative R) (source_increment v negative R hRi)
  intro before input emitted
  exact DenseRegularRecord.unboxed_hoareTime right payload j vs hcap occ hocc hrow t v B negative hB ht hcoef hI hM hbits
    before input emitted R hRa hRp hRf

end JointThermoComplexity.Complexity.DenseRegularAdvance

#print axioms JointThermoComplexity.Complexity.DenseRegularAdvance.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseRegularAdvance.unboxed_hoareTime
