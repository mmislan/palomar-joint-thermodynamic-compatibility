module
public import proofs.JointThermoComplexity.Complexity.DenseTemplateDegree

set_option autoImplicit false
@[expose] public section

/-! Actual boxed and unboxed external power blocks retain the loaded source fields. -/

namespace JointThermoComplexity.Complexity.DenseExternalPower
open _root_.Complexity _root_.Complexity.TM BinaryIncrementRun
open HeaderAt (Cursor)
variable {n : ℕ}

def Pre (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n : ℕ)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop) : _root_.Complexity.TM.TapePred 64 :=
  fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
    Register 0 (work DensePowerPorts.index) ∧ PowerVectorUnit.Refs (DensePowerPorts.cellLayout m hm) values work ∧
    IsReg n (work DenseParserPorts.arity) ∧ R work

def vectorBound (n B : ℕ) : ℕ := ReusablePowerVector.bound n n B

theorem vector_hoareTime (m : ℕ) (hm : m ≤ 4) (weights : SmallCoefficientMatch.Ports 63 → ℕ)
    (values : Fin 64 → ℕ) (n B : ℕ)
    (hbits : ∀ p ∈ (DensePowerPorts.cellLayout m hm).comparisons, (values p.constant).bits.length ≤ B)
    (hweight : PowerCellWord.weight (PowerCellEmit.items (DensePowerPorts.cellLayout m hm).comparisons weights) ≤ 4)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop)
    (hR : PowerVectorLoop.Stable (DensePowerPorts.layout m hm) R) :
    (ReusablePowerVector.machine (DensePowerPorts.layout m hm) weights).HoareTime
      (Pre m hm values n before input emitted R)
      (Pre m hm values n before input
        (emitted ++ PowerVectorControl.words (DensePowerPorts.cellLayout m hm) weights values 0 n) R)
      (vectorBound n B) := by
  have hh := ReusablePowerVector.hoareTime (DensePowerPorts.layout m hm) weights values 0 n n B (by omega)
    hbits (DensePowerPorts.count m hm) hweight before input emitted R hR
  apply hh.consequence
  · rintro inp work out ⟨hc, hs, hi, hr, hf, hx⟩
    exact ⟨⟨hc, hs, hi, hr, hx⟩, hf⟩
  · rintro inp work out ⟨⟨hc, hs, hi, hr, hx⟩, hf⟩
    exact ⟨hc, hs, hi, hr, hf, hx⟩
  · exact le_rfl

def boxedMachine (m : ℕ) (hm : m ≤ 4) (occ : List (Fin m)) : TM 64 :=
  ReusablePowerVector.machine (DensePowerPorts.layout m hm) (OccurrencePowerWeights.weight occ)

theorem boxed_hoareTime (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length))
    (hocc : occ.length ≤ 4) (B : ℕ) (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop)
    (hR : PowerVectorLoop.Stable (DensePowerPorts.layout vs.length hcap) R) :
    (boxedMachine vs.length hcap occ).HoareTime
      (Pre vs.length hcap (DensePowerReady.values vs) n before input emitted R)
      (Pre vs.length hcap (DensePowerReady.values vs) n before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (fun v : Fin n => (occ.map (RawNormalizationTemplates.lookup vs)).count v)) R) (vectorBound n B) := by
  have hw : PowerCellWord.weight (PowerCellEmit.items (DensePowerPorts.cellLayout vs.length hcap).comparisons
      (OccurrencePowerWeights.weight occ)) ≤ 4 := by rw [OccurrencePowerWeights.weight_total]; exact hocc
  have hh := vector_hoareTime vs.length hcap (OccurrencePowerWeights.weight occ) (DensePowerReady.values vs) n B
    (DensePowerReady.bits vs hcap B hbits) hw before input emitted R hR
  simpa only [boxedMachine, DenseTemplatePowerCode.boxed_code] using hh

def unboxedMachine (m : ℕ) (hm : m ≤ 4) (occ : List (Fin m ⊕ Fin m)) : TM 64 :=
  seqTM (emitBitsTM (BitCodec.naturalCode 0))
    (seqTM (boxedMachine m hm (DenseTemplatePowerCode.positive occ))
      (boxedMachine m hm (DenseTemplatePowerCode.negative occ)))

def unboxedBound (n B : ℕ) : ℕ := 2 * vectorBound n B + (BitCodec.naturalCode 0).length + 2

theorem unboxed_hoareTime (vs : List (Fin n)) (hcap : vs.length ≤ 4) (occ : List (Fin vs.length ⊕ Fin vs.length))
    (hocc : occ.length ≤ 4) (B : ℕ) (hbits : ∀ i : Fin vs.length, vs[i.val].val.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 64 → Tape) → Prop)
    (hR : PowerVectorLoop.Stable (DensePowerPorts.layout vs.length hcap) R) :
    (unboxedMachine vs.length hcap occ).HoareTime
      (Pre vs.length hcap (DensePowerReady.values vs) n before input emitted R)
      (Pre vs.length hcap (DensePowerReady.values vs) n before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (Fin.cons 0 (fun v : Fin (n + n) => (DenseTemplatePowerCode.signedMonomial vs occ).count v))) R)
      (unboxedBound n B) := by
  let vp := PowerVectorControl.words (DensePowerPorts.cellLayout vs.length hcap)
    (OccurrencePowerWeights.weight (DenseTemplatePowerCode.positive occ)) (DensePowerReady.values vs) 0 n
  let vn := PowerVectorControl.words (DensePowerPorts.cellLayout vs.length hcap)
    (OccurrencePowerWeights.weight (DenseTemplatePowerCode.negative occ)) (DensePowerReady.values vs) 0 n
  have hpw : PowerCellWord.weight (PowerCellEmit.items (DensePowerPorts.cellLayout vs.length hcap).comparisons
      (OccurrencePowerWeights.weight (DenseTemplatePowerCode.positive occ))) ≤ 4 := by
    rw [OccurrencePowerWeights.weight_total]
    exact (DenseTemplatePowerCode.positive_length occ).trans hocc
  have hnw : PowerCellWord.weight (PowerCellEmit.items (DensePowerPorts.cellLayout vs.length hcap).comparisons
      (OccurrencePowerWeights.weight (DenseTemplatePowerCode.negative occ))) ≤ 4 := by
    rw [OccurrencePowerWeights.weight_total]
    exact (DenseTemplatePowerCode.negative_length occ).trans hocc
  have hb := DensePowerReady.bits vs hcap B hbits
  have hp := vector_hoareTime vs.length hcap (OccurrencePowerWeights.weight (DenseTemplatePowerCode.positive occ))
    (DensePowerReady.values vs) n B hb hpw before input (emitted ++ BitCodec.naturalCode 0) R hR
  have hn := vector_hoareTime vs.length hcap (OccurrencePowerWeights.weight (DenseTemplatePowerCode.negative occ))
    (DensePowerReady.values vs) n B hb hnw before input ((emitted ++ BitCodec.naturalCode 0) ++ vp) R hR
  have hv := seqTM_hoareTime _ _ hp (by
    intro inp work out hx
    obtain ⟨hi, hw, ho⟩ := hx.1.phase
    rw [hi, hw, ho]
    exact hx) hn
  let S : (Fin 64 → Tape) → Prop := fun work => Register 0 (work DensePowerPorts.index) ∧
    PowerVectorUnit.Refs (DensePowerPorts.cellLayout vs.length hcap) (DensePowerReady.values vs) work ∧
    IsReg n (work DenseParserPorts.arity) ∧ R work
  have hz := FixedOutput.hoareTime (BitCodec.naturalCode 0) before input emitted S
  have hall := seqTM_hoareTime _ _ hz (by
    intro inp work out hx
    obtain ⟨hi, hw, ho⟩ := hx.1.phase
    rw [hi, hw, ho]
    exact hx) hv
  apply hall.consequence
  · exact fun _ _ _ hp => hp
  · rintro inp work out ⟨hc, hs, hi, hr, hf, hx⟩
    refine ⟨?_, hs, hi, hr, hf, hx⟩
    change Cursor before input (((emitted ++ BitCodec.naturalCode 0) ++ vp) ++ vn) inp work out at hc
    rw [DenseTemplatePowerCode.unboxed_code vs hcap occ]
    simpa only [vp, vn, List.append_assoc] using hc
  · unfold unboxedBound
    omega

theorem polynomial_vectorBound (n B : ℕ) : vectorBound n B = n * (98 * n + 96 * B + 114) + 3 * n + 12 :=
  ReusablePowerVector.polynomial_bound n n B

end JointThermoComplexity.Complexity.DenseExternalPower

#print axioms JointThermoComplexity.Complexity.DenseExternalPower.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseExternalPower.unboxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseExternalPower.polynomial_vectorBound
