module
public import proofs.JointThermoComplexity.Complexity.DenseRawRecord
public import proofs.JointThermoComplexity.Complexity.DenseFixedAdvance

set_option autoImplicit false
@[expose] public section

/-! Baseline/offset machines at a generic retained reference bank. All numeric
dimensions and the offset are raw tape values, independent of source validity. -/

namespace JointThermoComplexity.Complexity.DenseFixedRawRecord
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseRecordFrame DenseComplexOriginal
open DenseFixedRecord (Source source_stable)

def word (boxed right offset : Bool) (U N : ℕ) (i : Fin (N + 2)) (e : ℕ) (gamma : Fin e → ℕ) : List Bool :=
  (DenseRawRecord.reactWord right N i e gamma ++ DenseRawProduct.word right N i e gamma) ++
    DenseFactorCode.fixedWord boxed right offset U

theorem factor_hoareTime (boxed right offset : Bool) (U B : ℕ) (hB : U.bits.length ≤ B)
    (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N : ℕ) (i : Fin (N + 2))
    (R : (Fin 64 → Tape) → Prop) (before input emitted : List Bool) :
    (DenseFixedFactor.machine boxed right offset).HoareTime (Pre m hm values n N i before input emitted (Source U R))
      (Pre m hm values n N i before input (emitted ++ DenseFactorCode.fixedWord boxed right offset U) (Source U R))
      (3 * B + 11) := by
  have hh := DenseFixedFactor.hoareTime boxed right offset U B hB before input emitted (Fields m hm values n N i R)
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hi, hn, hf, hz, hh, hN, hb, href, ha, hu, hr⟩
    exact ⟨hc, hs, hu, hi, hn, hf, hz, hh, hN, hb, href, ha, hr⟩
  · rintro inp work out ⟨hc, hs, hu, hi, hn, hf, hz, hh, hN, hb, href, ha, hr⟩
    exact ⟨hc, hs, hi, hn, hf, hz, hh, hN, hb, href, ha, hu, hr⟩
  · exact le_rfl

theorem hoareTime (boxed right offset : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N U B : ℕ)
    (i : Fin (N + 2)) (e : ℕ) (gamma : Fin e → ℕ) (external : TM 64) (E : ℕ)
    (he : DenseComplexCore.Emits external m hm values n (FiniteCodec.functionCode FiniteCodec.natural gamma) E)
    (hU : U.bits.length ≤ B) (hI : i.val.bits.length ≤ B) (hM : (vertex true i).val.bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R)
    (before input emitted : List Bool) :
    (DenseFixedRecord.machine boxed right offset external).HoareTime (Pre m hm values n N i before input emitted (Source U R))
      (Pre m hm values n N i before input (emitted ++ word boxed right offset U N i e gamma) (Source U R))
      (DenseFixedRecord.timeBound right N B E) := by
  let S := Source U R
  have hSa := source_stable false U R hRa
  have hSp := source_stable true U R hRp
  have ha := DenseComplexCore.code_hoareTime right false m hm values n N (vertex false i).val B 1 e hI external gamma E he
    before input emitted (ReactR i S) (react_stable i S hSa)
  have h1 := ha.consequence
    (fun inp work out h => (react_iff m hm values n N i before input emitted S inp work out).mp h)
    (fun inp work out h => (react_iff m hm values n N i before input (emitted ++ DenseRawRecord.reactWord right N i e gamma) S inp work out).mpr h) le_rfl
  have hp := DenseRawProduct.hoareTime right m hm values n N B i e gamma hM external E he
    before input (emitted ++ DenseRawRecord.reactWord right N i e gamma) (ProductR i S) (product_stable i S hSp)
  have h2 := hp.consequence
    (fun inp work out h => (product_iff m hm values n N i before input (emitted ++ DenseRawRecord.reactWord right N i e gamma) S inp work out).mp h)
    (fun inp work out h => (product_iff m hm values n N i before input
      ((emitted ++ DenseRawRecord.reactWord right N i e gamma) ++ DenseRawProduct.word right N i e gamma) S inp work out).mpr h) le_rfl
  have h12 := seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) h2
  have hh := seqTM_hoareTime _ _ h12 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) (factor_hoareTime boxed right offset U B hU m hm values n N i R before input
      ((emitted ++ DenseRawRecord.reactWord right N i e gamma) ++ DenseRawProduct.word right N i e gamma))
  apply hh.consequence (fun _ _ _ h => h)
  · intro inp work out h
    simpa only [word, List.append_assoc] using h
  · unfold DenseFixedRecord.timeBound
    omega

theorem advanced_hoareTime (boxed right offset : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N U B : ℕ)
    (i : Fin (N + 2)) (e : ℕ) (gamma : Fin e → ℕ) (external : TM 64) (E : ℕ)
    (he : DenseComplexCore.Emits external m hm values n (FiniteCodec.functionCode FiniteCodec.natural gamma) E)
    (hU : U.bits.length ≤ B) (hI : i.val.bits.length ≤ B) (hM : (vertex true i).val.bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R)
    (hRi : BinaryIncrementFramed.Stable (38 : Fin 64) R) (before input emitted : List Bool) :
    (DenseRecordAdvance.machine (DenseFixedRecord.machine boxed right offset external)).HoareTime
      (Pre m hm values n N i before input emitted (Source U R))
      (DenseRecordAdvance.At (i.val + 1) m hm values n N i before input
        (emitted ++ word boxed right offset U N i e gamma) (Source U R)) (DenseFixedRecord.timeBound right N B E + 2 * B + 5) := by
  have hr := hoareTime boxed right offset m hm values n N U B i e gamma external E he hU hI hM R hRa hRp before input emitted
  have hi := BinaryIncrementFramed.bounded_hoareTime (38 : Fin 64) i.val B hI before input
    (emitted ++ word boxed right offset U N i e gamma) (DenseRecordAdvance.Tail m hm values n N i (Source U R))
    (DenseRecordAdvance.tail_stable m hm values n N i (Source U R) (DenseFixedAdvance.source_increment U R hRi))
  have hh := seqTM_hoareTime _ _ hr (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) hi
  exact hh.mono_bound (by omega)

theorem boxed_hoareTime (right offset : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N U B : ℕ)
    (i : Fin (N + 2)) (hU : U.bits.length ≤ B) (hI : i.val.bits.length ≤ B) (hM : (vertex true i).val.bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R)
    (before input emitted : List Bool) :
    (DenseFixedRecord.machine true right offset DenseFixedExternalPower.boxedMachine).HoareTime
      (Pre m hm values n N i before input emitted (Source U R))
      (Pre m hm values n N i before input (emitted ++ word true right offset U N i n (fun _ => 0)) (Source U R))
      (DenseFixedRecord.timeBound right N B (DenseFixedExternalPower.boxedBound n)) :=
  hoareTime true right offset m hm values n N U B i n _ _ _ (DenseFixedExternalPower.boxed_emits m hm values n)
    hU hI hM R hRa hRp before input emitted

theorem unboxed_hoareTime (right offset : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N U B : ℕ)
    (i : Fin (N + 2)) (hU : U.bits.length ≤ B) (hI : i.val.bits.length ≤ B) (hM : (vertex true i).val.bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hRa : DenseComplexPorts.Stable false R) (hRp : DenseComplexPorts.Stable true R)
    (before input emitted : List Bool) :
    (DenseFixedRecord.machine false right offset (DenseFixedExternalPower.unboxedMachine (DenseFixedComplexOriginal.offsetPower offset))).HoareTime
      (Pre m hm values n N i before input emitted (Source U R))
      (Pre m hm values n N i before input (emitted ++ word false right offset U N i ((n + n) + 1)
        (Fin.cons (DenseFixedComplexOriginal.offsetPower offset) (fun _ => 0))) (Source U R))
      (DenseFixedRecord.timeBound right N B (DenseFixedExternalPower.unboxedBound n (DenseFixedComplexOriginal.offsetPower offset))) :=
  hoareTime false right offset m hm values n N U B i ((n + n) + 1) _ _ _
    (DenseFixedExternalPower.unboxed_emits m hm values n (DenseFixedComplexOriginal.offsetPower offset))
    hU hI hM R hRa hRp before input emitted

end JointThermoComplexity.Complexity.DenseFixedRawRecord

#print axioms JointThermoComplexity.Complexity.DenseFixedRawRecord.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseFixedRawRecord.unboxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseFixedRawRecord.advanced_hoareTime
