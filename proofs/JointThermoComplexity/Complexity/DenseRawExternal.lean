module
public import proofs.JointThermoComplexity.Complexity.DenseEndRegister

set_option autoImplicit false
@[expose] public section

/-! The unchanged external machines on arbitrary binary references, including
values outside the structural arity on malformed raw inputs. -/

namespace JointThermoComplexity.Complexity.DenseRawExternal
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open DenseComplexCore

def boxedGamma (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (occ : List (Fin m)) (n : ℕ) : Fin n → ℕ :=
  fun j => PowerVectorControl.cell (DensePowerPorts.cellLayout m hm) (OccurrencePowerWeights.weight occ) values j.val
def unboxedGamma (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (occ : List (Fin m ⊕ Fin m)) (n : ℕ) :
    Fin ((n + n) + 1) → ℕ :=
  Fin.cons 0 (Fin.append (boxedGamma m hm values (DenseTemplatePowerCode.positive occ) n)
    (boxedGamma m hm values (DenseTemplatePowerCode.negative occ) n))

theorem boxed_emits (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (occ : List (Fin m)) (hocc : occ.length ≤ 4)
    (n B : ℕ) (hbits : ∀ p ∈ (DensePowerPorts.cellLayout m hm).comparisons, (values p.constant).bits.length ≤ B) :
    Emits (DenseExternalPower.boxedMachine m hm occ) m hm values n
      (FiniteCodec.functionCode FiniteCodec.natural (boxedGamma m hm values occ n)) (DenseExternalPower.vectorBound n B) := by
  intro before input emitted R hR
  have hw : PowerCellWord.weight (PowerCellEmit.items (DensePowerPorts.cellLayout m hm).comparisons
      (OccurrencePowerWeights.weight occ)) ≤ 4 := by rw [OccurrencePowerWeights.weight_total]; exact hocc
  have hh := DenseExternalPower.vector_hoareTime m hm (OccurrencePowerWeights.weight occ) values n B hbits hw
    before input emitted R hR
  have hc : PowerVectorControl.words (DensePowerPorts.cellLayout m hm) (OccurrencePowerWeights.weight occ) values 0 n =
      FiniteCodec.functionCode FiniteCodec.natural (boxedGamma m hm values occ n) := by
    rw [PowerVectorControl.words_code]
    simp only [Nat.zero_add]
    rfl
  apply hh.consequence (fun _ _ _ h => h)
  · intro inp work out h
    rw [← hc]
    exact h
  · exact le_rfl

theorem unboxed_code (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (occ : List (Fin m ⊕ Fin m)) (n : ℕ) :
    FiniteCodec.functionCode FiniteCodec.natural (unboxedGamma m hm values occ n) =
      BitCodec.naturalCode 0 ++
        (FiniteCodec.functionCode FiniteCodec.natural (boxedGamma m hm values (DenseTemplatePowerCode.positive occ) n) ++
        FiniteCodec.functionCode FiniteCodec.natural (boxedGamma m hm values (DenseTemplatePowerCode.negative occ) n)) := by
  have hh := DenseBlockWords.code_append FiniteCodec.natural
    (boxedGamma m hm values (DenseTemplatePowerCode.positive occ) n)
    (boxedGamma m hm values (DenseTemplatePowerCode.negative occ) n)
  simpa only [unboxedGamma, FiniteCodec.functionCode, Fin.cons_zero, Fin.cons_succ, FiniteCodec.natural] using
    congrArg (fun rest => BitCodec.naturalCode 0 ++ rest) hh

theorem unboxed_emits (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (occ : List (Fin m ⊕ Fin m)) (hocc : occ.length ≤ 4)
    (n B : ℕ) (hbits : ∀ p ∈ (DensePowerPorts.cellLayout m hm).comparisons, (values p.constant).bits.length ≤ B) :
    Emits (DenseExternalPower.unboxedMachine m hm occ) m hm values n
      (FiniteCodec.functionCode FiniteCodec.natural (unboxedGamma m hm values occ n)) (DenseExternalPower.unboxedBound n B) := by
  intro before input emitted R hR
  let zp := FiniteCodec.functionCode FiniteCodec.natural (boxedGamma m hm values (DenseTemplatePowerCode.positive occ) n)
  let zn := FiniteCodec.functionCode FiniteCodec.natural (boxedGamma m hm values (DenseTemplatePowerCode.negative occ) n)
  have hp := boxed_emits m hm values (DenseTemplatePowerCode.positive occ)
    ((DenseTemplatePowerCode.positive_length occ).trans hocc) n B hbits before input (emitted ++ BitCodec.naturalCode 0) R hR
  have hn := boxed_emits m hm values (DenseTemplatePowerCode.negative occ)
    ((DenseTemplatePowerCode.negative_length occ).trans hocc) n B hbits before input ((emitted ++ BitCodec.naturalCode 0) ++ zp) R hR
  have hpn := seqTM_hoareTime _ _ hp (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) hn
  let S : (Fin 64 → Tape) → Prop := fun work => Register 0 (work DensePowerPorts.index) ∧
    PowerVectorUnit.Refs (DensePowerPorts.cellLayout m hm) values work ∧ IsReg n (work 16) ∧ R work
  have h0 := FixedOutput.hoareTime (BitCodec.naturalCode 0) before input emitted S
  have hh := seqTM_hoareTime _ _ h0 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) hpn
  apply hh.consequence (fun _ _ _ h => h)
  · intro inp work out h
    rw [unboxed_code]
    simpa only [zp, zn, List.append_assoc] using h
  · unfold DenseExternalPower.unboxedBound
    omega

end JointThermoComplexity.Complexity.DenseRawExternal

#print axioms JointThermoComplexity.Complexity.DenseRawExternal.boxed_emits
#print axioms JointThermoComplexity.Complexity.DenseRawExternal.unboxed_emits
