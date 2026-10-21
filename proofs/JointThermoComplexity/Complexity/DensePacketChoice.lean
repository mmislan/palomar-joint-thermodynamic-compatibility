module
public import proofs.JointThermoComplexity.Complexity.DenseSourceBank

set_option autoImplicit false
@[expose] public section

/-! One finite boxed/unboxed template packet returns the complete source state. -/

namespace JointThermoComplexity.Complexity.DensePacketChoice
open _root_.Complexity _root_.Complexity.TM
open DenseSourceFrame

def machine (boxed right : Bool) (m : ℕ) (hm : m ≤ 4) : TM 64 :=
  if boxed then DenseFourTemplatePacket.boxedMachine right m hm else DenseFourTemplatePacket.unboxedMachine right m hm
def words (boxed right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N v : ℕ) (negative : Bool) (current : ℕ) : List Bool :=
  if boxed then DenseFourTemplatePacket.boxedWords right m hm values n N v negative current
  else DenseFourTemplatePacket.unboxedWords right m hm values n N v negative current
def timeBound (boxed right : Bool) (n N B : ℕ) : ℕ :=
  if boxed then DenseTemplatePacket.boxedBound right n N B else DenseTemplatePacket.unboxedBound right n N B

theorem hoareTime (boxed right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (L n N B v : ℕ) (negative : Bool)
    (hB : v.bits.length ≤ B) (hbase : N + 2 ≤ B)
    (hbits : ∀ p ∈ (DensePowerPorts.cellLayout 4 (by decide)).comparisons, (values p.constant).bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hR : Stable R) (before input : List Bool)
    (current : ℕ) (hfit : current + 2 ^ m ≤ N + 2) (emitted : List Bool) :
    (machine boxed right m hm).HoareTime
      (DensePacketControl.Pre current 4 (by decide) values n N v negative before input emitted (PacketR L R))
      (Pre L n N (current + 2 ^ m) before input (emitted ++ words boxed right m hm values n N v negative current) R)
      (timeBound boxed right n N B) := by
  cases boxed with
  | false =>
    have hh := DenseFourTemplatePacket.unboxed_hoareTime right m hm values n N B v negative hB hbase hbits
      (PacketR L R) (packet_stable L R hR) before input current
      (by simpa only [RawNormalizationTemplates.length_orthantTemplate] using hfit) emitted
    apply hh.consequence (fun _ _ _ h => h)
    · intro inp work out h
      have hp := packet_post L n N (current + (RawNormalizationTemplates.orthantTemplate m).length) v negative values R before input
        (emitted ++ DenseFourTemplatePacket.unboxedWords right m hm values n N v negative current) inp work out h
      simpa only [words, Bool.false_eq_true, ↓reduceIte, RawNormalizationTemplates.length_orthantTemplate] using hp
    · exact le_rfl
  | true =>
    have hh := DenseFourTemplatePacket.boxed_hoareTime right m hm values n N B v negative hB hbase hbits
      (PacketR L R) (packet_stable L R hR) before input current
      (by simpa only [RawNormalizationTemplates.length_cubeTemplate] using hfit) emitted
    apply hh.consequence (fun _ _ _ h => h)
    · intro inp work out h
      have hp := packet_post L n N (current + (RawNormalizationTemplates.cubeTemplate 4 m).length) v negative values R before input
        (emitted ++ DenseFourTemplatePacket.boxedWords right m hm values n N v negative current) inp work out h
      simpa only [words, ↓reduceIte, RawNormalizationTemplates.length_cubeTemplate] using hp
    · exact le_rfl

end JointThermoComplexity.Complexity.DensePacketChoice

#print axioms JointThermoComplexity.Complexity.DensePacketChoice.hoareTime
