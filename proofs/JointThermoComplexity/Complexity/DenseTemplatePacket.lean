module
public import proofs.JointThermoComplexity.Complexity.DenseRawPacket
public import proofs.JointThermoComplexity.Complexity.DegreeFourTemplates

set_option autoImplicit false
@[expose] public section

/-! Concrete complete-record packets for the unchanged ordered normalization
tables. Every row program is compiled before reading the source data. -/

namespace JointThermoComplexity.Complexity.DenseTemplatePacket
open _root_.Complexity _root_.Complexity.TM
open RawNormalizationTemplates DensePacketControl

def boxedExternal (m : ℕ) (hm : m ≤ 4) (row : ℤ × List (Fin m)) : TM 64 :=
  DenseExternalPower.boxedMachine m hm row.2
def unboxedExternal (m : ℕ) (hm : m ≤ 4) (row : ℤ × List (Fin m ⊕ Fin m)) : TM 64 :=
  DenseExternalPower.unboxedMachine m hm row.2
def boxedMachine (right : Bool) (m : ℕ) (hm : m ≤ 4) : TM 64 :=
  machine right (boxedExternal m hm) Prod.fst (cubeTemplate 4 m)
def unboxedMachine (right : Bool) (m : ℕ) (hm : m ≤ 4) : TM 64 :=
  machine right (unboxedExternal m hm) Prod.fst (orthantTemplate m)

def boxedWords (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N v : ℕ) (negative : Bool) (current : ℕ) : List Bool :=
  words right N n (fun row : ℤ × List (Fin m) => DenseRawExternal.boxedGamma m hm values row.2 n) Prod.fst
    v negative current (cubeTemplate 4 m)
def unboxedWords (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N v : ℕ) (negative : Bool) (current : ℕ) : List Bool :=
  words right N ((n + n) + 1) (fun row : ℤ × List (Fin m ⊕ Fin m) => DenseRawExternal.unboxedGamma m hm values row.2 n) Prod.fst
    v negative current (orthantTemplate m)

def boxedBound (right : Bool) (n N B : ℕ) : ℕ := timeBound right N B (DenseExternalPower.vectorBound n B) 16
def unboxedBound (right : Bool) (n N B : ℕ) : ℕ := timeBound right N B (DenseExternalPower.unboxedBound n B) 16

theorem boxed_hoareTime (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N B v : ℕ) (negative : Bool)
    (hB : v.bits.length ≤ B) (hbase : N + 2 ≤ B)
    (hbits : ∀ p ∈ (DensePowerPorts.cellLayout m hm).comparisons, (values p.constant).bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hR : DenseRowFrame.Stable R) (before input : List Bool)
    (current : ℕ) (hfit : current + (cubeTemplate 4 m).length ≤ N + 2) (emitted : List Bool) :
    (boxedMachine right m hm).HoareTime (Pre current m hm values n N v negative before input emitted R)
      (Pre (current + (cubeTemplate 4 m).length) m hm values n N v negative before input
        (emitted ++ boxedWords right m hm values n N v negative current) R) (boxedBound right n N B) := by
  have hc : ∀ row ∈ cubeTemplate 4 m, row.1.natAbs ≤ 81 := fun row hrow =>
    (DegreeFourTemplates.cube_magnitude_bounds m hm row hrow).2
  have he : ∀ row ∈ cubeTemplate 4 m, DenseComplexCore.Emits (boxedExternal m hm row) m hm values n
      (FiniteCodec.functionCode FiniteCodec.natural (DenseRawExternal.boxedGamma m hm values row.2 n)) (DenseExternalPower.vectorBound n B) := by
    intro row hrow
    exact DenseRawExternal.boxed_emits m hm values row.2 (DenseTemplateDegree.cube_degree hm row hrow) n B hbits
  have hh := DenseRawPacket.hoareTime right m hm values n N B n (DenseExternalPower.vectorBound n B)
    (boxedExternal m hm) Prod.fst (fun row => DenseRawExternal.boxedGamma m hm values row.2 n)
    v negative hB hbase R hR before input (cubeTemplate 4 m) hc he current hfit emitted
  exact hh.mono_bound (Nat.mul_le_mul_right _ (DegreeFourTemplates.cube_length_le m hm))

theorem unboxed_hoareTime (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N B v : ℕ) (negative : Bool)
    (hB : v.bits.length ≤ B) (hbase : N + 2 ≤ B)
    (hbits : ∀ p ∈ (DensePowerPorts.cellLayout m hm).comparisons, (values p.constant).bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hR : DenseRowFrame.Stable R) (before input : List Bool)
    (current : ℕ) (hfit : current + (orthantTemplate m).length ≤ N + 2) (emitted : List Bool) :
    (unboxedMachine right m hm).HoareTime (Pre current m hm values n N v negative before input emitted R)
      (Pre (current + (orthantTemplate m).length) m hm values n N v negative before input
        (emitted ++ unboxedWords right m hm values n N v negative current) R) (unboxedBound right n N B) := by
  have hc : ∀ row ∈ orthantTemplate m, row.1.natAbs ≤ 81 := by
    intro row hrow
    rw [DegreeFourTemplates.orthant_magnitude m hm row hrow]
    decide
  have he : ∀ row ∈ orthantTemplate m, DenseComplexCore.Emits (unboxedExternal m hm row) m hm values n
      (FiniteCodec.functionCode FiniteCodec.natural (DenseRawExternal.unboxedGamma m hm values row.2 n)) (DenseExternalPower.unboxedBound n B) := by
    intro row hrow
    exact DenseRawExternal.unboxed_emits m hm values row.2 (DenseTemplateDegree.orthant_degree hm row hrow) n B hbits
  have hh := DenseRawPacket.hoareTime right m hm values n N B ((n + n) + 1) (DenseExternalPower.unboxedBound n B)
    (unboxedExternal m hm) Prod.fst (fun row => DenseRawExternal.unboxedGamma m hm values row.2 n)
    v negative hB hbase R hR before input (orthantTemplate m) hc he current hfit emitted
  exact hh.mono_bound (Nat.mul_le_mul_right _ (DegreeFourTemplates.orthant_length_le m hm))

end JointThermoComplexity.Complexity.DenseTemplatePacket

#print axioms JointThermoComplexity.Complexity.DenseTemplatePacket.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseTemplatePacket.unboxed_hoareTime
