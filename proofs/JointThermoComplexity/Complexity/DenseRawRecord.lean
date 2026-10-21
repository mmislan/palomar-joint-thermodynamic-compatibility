module
public import proofs.JointThermoComplexity.Complexity.DenseRawFactor

set_option autoImplicit false
@[expose] public section

/-! The canonical regular-record machines also run on arbitrary raw binary
reference values. No polynomial, row identity, or valid reference bound is needed. -/

namespace JointThermoComplexity.Complexity.DenseRawRecord
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseRecordFrame DenseComplexOriginal
open DenseRegularRecord (Source source_stable)
variable {N : ℕ}

def reactWord (right : Bool) (N : ℕ) (i : Fin (N + 2)) (e : ℕ) (gamma : Fin e → ℕ) : List Bool :=
  FiniteCodec.functionCode FiniteCodec.natural (DenseComplexCore.values right 1 (vertex false i).val N e gamma)
def word (right : Bool) (N : ℕ) (i : Fin (N + 2)) (e : ℕ) (gamma : Fin e → ℕ) (t : ℤ) (v : ℕ) (negative : Bool) : List Bool :=
  (reactWord right N i e gamma ++ DenseRawProduct.word right N i e gamma) ++
    RationalFactorWords.word right (RationalFactorWords.coefficient negative v * t)

theorem factor_hoareTime (t : ℤ) (v B : ℕ) (negative right : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ) (i : Fin (N + 2))
    (R : (Fin 64 → Tape) → Prop) (hR : DenseFactorFrame.Stable R) (before input emitted : List Bool) :
    (DenseTemplateFactor.machine t right).HoareTime (Pre m hm values n N i before input emitted (Source v negative R))
      (Pre m hm values n N i before input
        (emitted ++ RationalFactorWords.word right (RationalFactorWords.coefficient negative v * t)) (Source v negative R))
      (11 * B + 872) := by
  have hh := DenseRawFactor.hoareTime t v B negative right hB ht before input emitted
    (Fields m hm values n N i R) (fields_factor_stable m hm values n N i R hR)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hi, hn, hf, hz, hh, hN, hb, href, ha, hv, hsign, hadj, hscratch, hstart, hr⟩
    exact ⟨hc, hs, hv, hsign, hadj, hscratch, hstart, hi, hn, hf, hz, hh, hN, hb, href, ha, hr⟩
  · rintro inp work out ⟨hc, hs, hv, hsign, hadj, hscratch, hstart, hi, hn, hf, hz, hh, hN, hb, href, ha, hr⟩
    exact ⟨hc, hs, hi, hn, hf, hz, hh, hN, hb, href, ha, hv, hsign, hadj, hscratch, hstart, hr⟩
  · exact le_rfl

theorem hoareTime (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N B : ℕ) (i : Fin (N + 2))
    (e : ℕ) (gamma : Fin e → ℕ) (external : TM 64) (E : ℕ)
    (he : DenseComplexCore.Emits external m hm values n (FiniteCodec.functionCode FiniteCodec.natural gamma) E)
    (t : ℤ) (v : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (hI : i.val.bits.length ≤ B) (hM : (vertex true i).val.bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hRa : DenseComplexPorts.Stable false R)
    (hRp : DenseComplexPorts.Stable true R) (hRf : DenseFactorFrame.Stable R) (before input emitted : List Bool) :
    (DenseRegularRecord.machine right external t).HoareTime (Pre m hm values n N i before input emitted (Source v negative R))
      (Pre m hm values n N i before input (emitted ++ word right N i e gamma t v negative) (Source v negative R))
      (DenseRegularRecord.timeBound right N B E) := by
  let S := Source v negative R
  have hSa := source_stable false v negative R hRa
  have hSp := source_stable true v negative R hRp
  have ha := DenseComplexCore.code_hoareTime right false m hm values n N (vertex false i).val B 1 e hI external gamma E he
    before input emitted (ReactR i S) (react_stable i S hSa)
  have h1 := ha.consequence
    (fun inp work out h => (react_iff m hm values n N i before input emitted S inp work out).mp h)
    (fun inp work out h => (react_iff m hm values n N i before input (emitted ++ reactWord right N i e gamma) S inp work out).mpr h) le_rfl
  have hp := DenseRawProduct.hoareTime right m hm values n N B i e gamma hM external E he
    before input (emitted ++ reactWord right N i e gamma) (ProductR i S) (product_stable i S hSp)
  have h2 := hp.consequence
    (fun inp work out h => (product_iff m hm values n N i before input (emitted ++ reactWord right N i e gamma) S inp work out).mp h)
    (fun inp work out h => (product_iff m hm values n N i before input
      ((emitted ++ reactWord right N i e gamma) ++ DenseRawProduct.word right N i e gamma) S inp work out).mpr h) le_rfl
  have h12 := seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) h2
  have hh := seqTM_hoareTime _ _ h12 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) (factor_hoareTime t v B negative right hB ht m hm values n N i R hRf before input
      ((emitted ++ reactWord right N i e gamma) ++ DenseRawProduct.word right N i e gamma))
  apply hh.consequence (fun _ _ _ h => h)
  · intro inp work out h
    simpa only [word, List.append_assoc] using h
  · unfold DenseRegularRecord.timeBound
    omega

theorem boxed_hoareTime (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N B : ℕ) (i : Fin (N + 2))
    (occ : List (Fin m)) (hocc : occ.length ≤ 4)
    (hbits : ∀ p ∈ (DensePowerPorts.cellLayout m hm).comparisons, (values p.constant).bits.length ≤ B)
    (t : ℤ) (v : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (hI : i.val.bits.length ≤ B) (hM : (vertex true i).val.bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hRa : DenseComplexPorts.Stable false R)
    (hRp : DenseComplexPorts.Stable true R) (hRf : DenseFactorFrame.Stable R) (before input emitted : List Bool) :
    (DenseRegularRecord.machine right (DenseExternalPower.boxedMachine m hm occ) t).HoareTime
      (Pre m hm values n N i before input emitted (Source v negative R))
      (Pre m hm values n N i before input
        (emitted ++ word right N i n (DenseRawExternal.boxedGamma m hm values occ n) t v negative) (Source v negative R))
      (DenseRegularRecord.timeBound right N B (DenseExternalPower.vectorBound n B)) :=
  hoareTime right m hm values n N B i n _ _ _ (DenseRawExternal.boxed_emits m hm values occ hocc n B hbits)
    t v negative hB ht hI hM R hRa hRp hRf before input emitted

theorem unboxed_hoareTime (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N B : ℕ) (i : Fin (N + 2))
    (occ : List (Fin m ⊕ Fin m)) (hocc : occ.length ≤ 4)
    (hbits : ∀ p ∈ (DensePowerPorts.cellLayout m hm).comparisons, (values p.constant).bits.length ≤ B)
    (t : ℤ) (v : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (hI : i.val.bits.length ≤ B) (hM : (vertex true i).val.bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hRa : DenseComplexPorts.Stable false R)
    (hRp : DenseComplexPorts.Stable true R) (hRf : DenseFactorFrame.Stable R) (before input emitted : List Bool) :
    (DenseRegularRecord.machine right (DenseExternalPower.unboxedMachine m hm occ) t).HoareTime
      (Pre m hm values n N i before input emitted (Source v negative R))
      (Pre m hm values n N i before input
        (emitted ++ word right N i ((n + n) + 1) (DenseRawExternal.unboxedGamma m hm values occ n) t v negative) (Source v negative R))
      (DenseRegularRecord.timeBound right N B (DenseExternalPower.unboxedBound n B)) :=
  hoareTime right m hm values n N B i ((n + n) + 1) _ _ _ (DenseRawExternal.unboxed_emits m hm values occ hocc n B hbits)
    t v negative hB ht hI hM R hRa hRp hRf before input emitted

theorem advanced_hoareTime (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N B : ℕ) (i : Fin (N + 2))
    (e : ℕ) (gamma : Fin e → ℕ) (external : TM 64) (E : ℕ)
    (he : DenseComplexCore.Emits external m hm values n (FiniteCodec.functionCode FiniteCodec.natural gamma) E)
    (t : ℤ) (v : ℕ) (negative : Bool) (hB : v.bits.length ≤ B) (ht : t.natAbs ≤ 81)
    (hI : i.val.bits.length ≤ B) (hM : (vertex true i).val.bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hRa : DenseComplexPorts.Stable false R)
    (hRp : DenseComplexPorts.Stable true R) (hRf : DenseFactorFrame.Stable R)
    (hRi : BinaryIncrementFramed.Stable (38 : Fin 64) R) (before input emitted : List Bool) :
    (DenseRecordAdvance.machine (DenseRegularRecord.machine right external t)).HoareTime
      (Pre m hm values n N i before input emitted (Source v negative R))
      (DenseRecordAdvance.At (i.val + 1) m hm values n N i before input
        (emitted ++ word right N i e gamma t v negative) (Source v negative R)) (DenseRegularRecord.timeBound right N B E + 2 * B + 5) := by
  have hr := hoareTime right m hm values n N B i e gamma external E he t v negative hB ht hI hM R hRa hRp hRf before input emitted
  have hi := BinaryIncrementFramed.bounded_hoareTime (38 : Fin 64) i.val B hI before input
    (emitted ++ word right N i e gamma t v negative) (DenseRecordAdvance.Tail m hm values n N i (Source v negative R))
    (DenseRecordAdvance.tail_stable m hm values n N i (Source v negative R) (DenseRegularAdvance.source_increment v negative R hRi))
  have hh := seqTM_hoareTime _ _ hr (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) hi
  exact hh.mono_bound (by omega)

end JointThermoComplexity.Complexity.DenseRawRecord

#print axioms JointThermoComplexity.Complexity.DenseRawRecord.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseRawRecord.unboxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseRawRecord.advanced_hoareTime
