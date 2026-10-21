module
public import proofs.JointThermoComplexity.Complexity.DenseRecordCore

set_option autoImplicit false
@[expose] public section

/-! Complete regular reaction records from fixed template programs. All source
values, signs and successor indices are read from the retained work tapes. -/

namespace JointThermoComplexity.Complexity.DenseRegularRecord
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseRecordCore DenseRecordFrame DenseComplexOriginal
variable {n : ℕ}

def Source (v : ℕ) (negative : Bool) (R : (Fin 64 → Tape) → Prop) (work : Fin 64 → Tape) : Prop :=
  Register v (work 0) ∧ (work 1).read = Γ.ofBool negative ∧ (work 12).head = 1 ∧
    (work 63).HasBinaryPrefix [] ∧ (work 63).cells 0 = Γ.start ∧ R work

theorem source_stable (product : Bool) (v : ℕ) (negative : Bool) (R : (Fin 64 → Tape) → Prop)
    (hR : DenseComplexPorts.Stable product R) : DenseComplexPorts.Stable product (Source v negative R) := by
  rintro work next he ⟨hv, hn, ha, hb, hz, hr⟩
  have keep (j : Fin 64) (hj : j = 0 ∨ j = 1 ∨ j = 12 ∨ j = 63) : next j = work j := by
    apply he j
    rcases hj with rfl | rfl | rfl | rfl <;> cases product <;>
      unfold DenseComplexPorts.Outside DenseComplexPorts.target <;> decide
  exact ⟨by rw [keep 0 (Or.inl rfl)]; exact hv,
    by rw [keep 1 (Or.inr (Or.inl rfl))]; exact hn,
    by rw [keep 12 (Or.inr (Or.inr (Or.inl rfl)))]; exact ha,
    by rw [keep 63 (Or.inr (Or.inr (Or.inr rfl)))]; exact hb,
    by rw [keep 63 (Or.inr (Or.inr (Or.inr rfl)))]; exact hz, hR work next he hr⟩

theorem factor_hoareTime (boxed right : Bool) (p : SparsePolynomialCodec.PolynomialData) (j : Fin p.payload.length)
    (t : ℤ) (v B : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (hcoef : RawChemicalPolynomial.coefficientInteger p.payload j = RationalFactorWords.coefficient negative v * t)
    (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n : ℕ)
    (R : (Fin 64 → Tape) → Prop) (hR : DenseFactorFrame.Stable R) (before input emitted : List Bool) :
    (DenseTemplateFactor.machine t right).HoareTime
      (Pre m hm values n p.payload.length j.succ.succ before input emitted (Source v negative R))
      (Pre m hm values n p.payload.length j.succ.succ before input
        (emitted ++ DenseFactorCode.factor right (RationalPolynomialNetwork.left boxed p)
          (RationalPolynomialNetwork.right boxed p) j.succ.succ) (Source v negative R)) (11 * B + 872) := by
  have hh := DenseFactorFrame.original_hoareTime boxed right p j t v B negative hB ht hcoef before input emitted
    (Fields m hm values n p.payload.length j.succ.succ R)
    (fields_factor_stable m hm values n p.payload.length j.succ.succ R hR)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hi, hn, hf, hz, hh, hN, hb, href, ha, hv, hsign, hadj, hscratch, hstart, hr⟩
    exact ⟨hc, hs, hv, hsign, hadj, hscratch, hstart, hi, hn, hf, hz, hh, hN, hb, href, ha, hr⟩
  · rintro inp work out ⟨hc, hs, hv, hsign, hadj, hscratch, hstart, hi, hn, hf, hz, hh, hN, hb, href, ha, hr⟩
    exact ⟨hc, hs, hi, hn, hf, hz, hh, hN, hb, href, ha, hv, hsign, hadj, hscratch, hstart, hr⟩
  · exact le_rfl

def machine (right : Bool) (external : TM 64) (t : ℤ) : TM 64 :=
  DenseRecordCore.machine (DenseComplexCore.machine right false 1 external)
    (DenseProductBranch.machine right external) (DenseTemplateFactor.machine t right)
def timeBound (right : Bool) (N B E : ℕ) : ℕ :=
  DenseComplexCore.bound right N B 1 E + DenseProductBranch.timeBound right N B E + (11 * B + 872) + 2

theorem boxed_hoareTime (right : Bool) (p : SparsePolynomialCodec.PolynomialData) (j : Fin p.payload.length)
    (vs : List (Fin p.arity)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length)) (hocc : occ.length ≤ 4)
    (hrow : p.payload[j.val].2 = occ.map (RawNormalizationTemplates.lookup vs))
    (t : ℤ) (v B : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (hcoef : RawChemicalPolynomial.coefficientInteger p.payload j = RationalFactorWords.coefficient negative v * t)
    (hI : j.succ.succ.val.bits.length ≤ B) (hM : (vertex true j.succ.succ).val.bits.length ≤ B)
    (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop)
    (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R) (hRf : DenseFactorFrame.Stable R) :
    (machine right (DenseExternalPower.boxedMachine vs.length hcap occ) t).HoareTime
      (Pre vs.length hcap (DensePowerReady.values vs) p.arity p.payload.length j.succ.succ before input emitted (Source v negative R))
      (Pre vs.length hcap (DensePowerReady.values vs) p.arity p.payload.length j.succ.succ before input
        (emitted ++ recordWord right (RationalPolynomialNetwork.left true p) (RationalPolynomialNetwork.right true p) j.succ.succ)
        (Source v negative R)) (timeBound right p.payload.length B (DenseExternalPower.vectorBound p.arity B)) := by
  apply DenseRecordCore.hoareTime _ _ _ right _ _ j.succ.succ vs.length hcap (DensePowerReady.values vs) p.arity
    (DenseComplexCore.bound right p.payload.length B 1 (DenseExternalPower.vectorBound p.arity B))
    (DenseProductBranch.timeBound right p.payload.length B (DenseExternalPower.vectorBound p.arity B)) (11 * B + 872)
    ?_ ?_ (Source v negative R) (source_stable false v negative R hRa) (source_stable true v negative R hRp)
    (factor_hoareTime true right p j t v B negative hB ht hcoef vs.length hcap (DensePowerReady.values vs) p.arity R hRf)
  · intro before input emitted S hS
    exact DenseComplexOriginal.boxed_hoareTime right false p j vs hcap occ hocc hrow B 1 rfl hI hbits before input emitted S hS
  · intro before input emitted S hS
    exact DenseProductEmit.boxed_hoareTime right p j vs hcap occ hocc hrow B hM hbits before input emitted S hS

theorem unboxed_hoareTime (right : Bool) (payload : SparseInteger.Poly (Fin (n + n))) (j : Fin payload.length)
    (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length ⊕ Fin vs.length)) (hocc : occ.length ≤ 4)
    (hrow : payload[j.val].2 = DenseTemplatePowerCode.signedMonomial vs occ)
    (t : ℤ) (v B : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (hcoef : RawChemicalPolynomial.coefficientInteger payload j = RationalFactorWords.coefficient negative v * t)
    (hI : j.succ.succ.val.bits.length ≤ B) (hM : (vertex true j.succ.succ).val.bits.length ≤ B)
    (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop)
    (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R) (hRf : DenseFactorFrame.Stable R) :
    (machine right (DenseExternalPower.unboxedMachine vs.length hcap occ) t).HoareTime
      (Pre vs.length hcap (DensePowerReady.values vs) n payload.length j.succ.succ before input emitted (Source v negative R))
      (Pre vs.length hcap (DensePowerReady.values vs) n payload.length j.succ.succ before input
        (emitted ++ recordWord right (RationalPolynomialNetwork.left false ⟨n + n, payload⟩)
          (RationalPolynomialNetwork.right false ⟨n + n, payload⟩) j.succ.succ) (Source v negative R))
      (timeBound right payload.length B (DenseExternalPower.unboxedBound n B)) := by
  apply DenseRecordCore.hoareTime _ _ _ right _ _ j.succ.succ vs.length hcap (DensePowerReady.values vs) n
    (DenseComplexCore.bound right payload.length B 1 (DenseExternalPower.unboxedBound n B))
    (DenseProductBranch.timeBound right payload.length B (DenseExternalPower.unboxedBound n B)) (11 * B + 872)
    ?_ ?_ (Source v negative R) (source_stable false v negative R hRa) (source_stable true v negative R hRp)
    (factor_hoareTime false right ⟨n + n, payload⟩ j t v B negative hB ht hcoef vs.length hcap (DensePowerReady.values vs) n R hRf)
  · intro before input emitted S hS
    exact DenseComplexOriginal.unboxed_hoareTime right false payload j vs hcap occ hocc hrow B 1 rfl hI hbits before input emitted S hS
  · intro before input emitted S hS
    exact DenseProductEmit.unboxed_hoareTime right payload j vs hcap occ hocc hrow B hM hbits before input emitted S hS

end JointThermoComplexity.Complexity.DenseRegularRecord

#print axioms JointThermoComplexity.Complexity.DenseRegularRecord.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseRegularRecord.unboxed_hoareTime
