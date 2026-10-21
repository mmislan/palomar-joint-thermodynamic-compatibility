module
public import proofs.JointThermoComplexity.Complexity.DenseReferenceBank

set_option autoImplicit false
@[expose] public section

/-! Finite normalization packets using one fixed four-port reference layout.
All four power-flag heads are returned through the same Refs invariant. -/

namespace JointThermoComplexity.Complexity.DenseFourTemplatePacket
open _root_.Complexity _root_.Complexity.TM
open RawNormalizationTemplates DensePacketControl

def boxedRows (m : ℕ) (hm : m ≤ 4) : List (ℤ × List (Fin 4)) :=
  (cubeTemplate 4 m).map (fun row => (row.1, row.2.map (Fin.castLE hm)))
def unboxedRows (m : ℕ) (hm : m ≤ 4) : List (ℤ × List (Fin 4 ⊕ Fin 4)) :=
  (orthantTemplate m).map (fun row => (row.1, row.2.map (Sum.map (Fin.castLE hm) (Fin.castLE hm))))

def boxedMachine (right : Bool) (m : ℕ) (hm : m ≤ 4) : TM 64 :=
  machine right (DenseTemplatePacket.boxedExternal 4 (by decide)) Prod.fst (boxedRows m hm)
def unboxedMachine (right : Bool) (m : ℕ) (hm : m ≤ 4) : TM 64 :=
  machine right (DenseTemplatePacket.unboxedExternal 4 (by decide)) Prod.fst (unboxedRows m hm)

def boxedWords (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N v : ℕ) (negative : Bool) (current : ℕ) : List Bool :=
  words right N n (fun row : ℤ × List (Fin 4) => DenseRawExternal.boxedGamma 4 (by decide) values row.2 n) Prod.fst
    v negative current (boxedRows m hm)
def unboxedWords (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N v : ℕ) (negative : Bool) (current : ℕ) : List Bool :=
  words right N ((n + n) + 1) (fun row : ℤ × List (Fin 4 ⊕ Fin 4) => DenseRawExternal.unboxedGamma 4 (by decide) values row.2 n) Prod.fst
    v negative current (unboxedRows m hm)

theorem boxed_bounded (m : ℕ) (hm : m ≤ 4) : ∀ row ∈ boxedRows m hm, row.1.natAbs ≤ 81 ∧ row.2.length ≤ 4 := by
  intro row hrow
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hrow
  exact ⟨(DegreeFourTemplates.cube_magnitude_bounds m hm a ha).2,
    by simpa only [List.length_map] using DenseTemplateDegree.cube_degree hm a ha⟩
theorem unboxed_bounded (m : ℕ) (hm : m ≤ 4) : ∀ row ∈ unboxedRows m hm, row.1.natAbs ≤ 81 ∧ row.2.length ≤ 4 := by
  intro row hrow
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hrow
  refine ⟨?_, by simpa only [List.length_map] using DenseTemplateDegree.orthant_degree hm a ha⟩
  rw [DegreeFourTemplates.orthant_magnitude m hm a ha]
  decide

theorem boxed_length (m : ℕ) (hm : m ≤ 4) : (boxedRows m hm).length = (cubeTemplate 4 m).length := List.length_map _
theorem unboxed_length (m : ℕ) (hm : m ≤ 4) : (unboxedRows m hm).length = (orthantTemplate m).length := List.length_map _

theorem lookup_cast (vs : List ℕ) (hm : vs.length ≤ 4) (i : Fin vs.length) :
    DenseRawReady.values vs (DenseReferenceBank.port (i.castLE hm)) = lookup vs i := by
  rw [DenseReferenceBank.values_port]
  change (if h : i.val < vs.length then vs[i.val] else 0) = lookup vs i
  rw [dite_eq_left i.isLt]
  rfl

theorem map_lookup (vs : List ℕ) (hm : vs.length ≤ 4) (occ : List (Fin vs.length)) :
    (occ.map (Fin.castLE hm)).map (fun i => DenseRawReady.values vs (DenseReferenceBank.port i)) = occ.map (lookup vs) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  exact lookup_cast vs hm i

theorem boxed_hoareTime (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N B v : ℕ) (negative : Bool)
    (hB : v.bits.length ≤ B) (hbase : N + 2 ≤ B)
    (hbits : ∀ p ∈ (DensePowerPorts.cellLayout 4 (by decide)).comparisons, (values p.constant).bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hR : DenseRowFrame.Stable R) (before input : List Bool)
    (current : ℕ) (hfit : current + (cubeTemplate 4 m).length ≤ N + 2) (emitted : List Bool) :
    (boxedMachine right m hm).HoareTime (Pre current 4 (by decide) values n N v negative before input emitted R)
      (Pre (current + (cubeTemplate 4 m).length) 4 (by decide) values n N v negative before input
        (emitted ++ boxedWords right m hm values n N v negative current) R) (DenseTemplatePacket.boxedBound right n N B) := by
  have hc : ∀ row ∈ boxedRows m hm, row.1.natAbs ≤ 81 := fun row hr => (boxed_bounded m hm row hr).1
  have he : ∀ row ∈ boxedRows m hm, DenseComplexCore.Emits (DenseTemplatePacket.boxedExternal 4 (by decide) row) 4 (by decide) values n
      (FiniteCodec.functionCode FiniteCodec.natural (DenseRawExternal.boxedGamma 4 (by decide) values row.2 n)) (DenseExternalPower.vectorBound n B) := by
    intro row hr
    exact DenseRawExternal.boxed_emits 4 (by decide) values row.2 (boxed_bounded m hm row hr).2 n B hbits
  have hh := DenseRawPacket.hoareTime right 4 (by decide) values n N B n (DenseExternalPower.vectorBound n B)
    (DenseTemplatePacket.boxedExternal 4 (by decide)) Prod.fst (fun row => DenseRawExternal.boxedGamma 4 (by decide) values row.2 n)
    v negative hB hbase R hR before input (boxedRows m hm) hc he current (by simpa only [boxed_length] using hfit) emitted
  have hlen : (boxedRows m hm).length ≤ 16 := (boxed_length m hm).trans_le (DegreeFourTemplates.cube_length_le m hm)
  apply hh.consequence (fun _ _ _ h => h)
  · intro inp work out h
    simpa only [boxed_length, boxedWords] using h
  · exact Nat.mul_le_mul_right _ hlen

theorem unboxed_hoareTime (right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N B v : ℕ) (negative : Bool)
    (hB : v.bits.length ≤ B) (hbase : N + 2 ≤ B)
    (hbits : ∀ p ∈ (DensePowerPorts.cellLayout 4 (by decide)).comparisons, (values p.constant).bits.length ≤ B)
    (R : (Fin 64 → Tape) → Prop) (hR : DenseRowFrame.Stable R) (before input : List Bool)
    (current : ℕ) (hfit : current + (orthantTemplate m).length ≤ N + 2) (emitted : List Bool) :
    (unboxedMachine right m hm).HoareTime (Pre current 4 (by decide) values n N v negative before input emitted R)
      (Pre (current + (orthantTemplate m).length) 4 (by decide) values n N v negative before input
        (emitted ++ unboxedWords right m hm values n N v negative current) R) (DenseTemplatePacket.unboxedBound right n N B) := by
  have hc : ∀ row ∈ unboxedRows m hm, row.1.natAbs ≤ 81 := fun row hr => (unboxed_bounded m hm row hr).1
  have he : ∀ row ∈ unboxedRows m hm, DenseComplexCore.Emits (DenseTemplatePacket.unboxedExternal 4 (by decide) row) 4 (by decide) values n
      (FiniteCodec.functionCode FiniteCodec.natural (DenseRawExternal.unboxedGamma 4 (by decide) values row.2 n)) (DenseExternalPower.unboxedBound n B) := by
    intro row hr
    exact DenseRawExternal.unboxed_emits 4 (by decide) values row.2 (unboxed_bounded m hm row hr).2 n B hbits
  have hh := DenseRawPacket.hoareTime right 4 (by decide) values n N B ((n + n) + 1) (DenseExternalPower.unboxedBound n B)
    (DenseTemplatePacket.unboxedExternal 4 (by decide)) Prod.fst (fun row => DenseRawExternal.unboxedGamma 4 (by decide) values row.2 n)
    v negative hB hbase R hR before input (unboxedRows m hm) hc he current (by simpa only [unboxed_length] using hfit) emitted
  have hlen : (unboxedRows m hm).length ≤ 16 := (unboxed_length m hm).trans_le (DegreeFourTemplates.orthant_length_le m hm)
  apply hh.consequence (fun _ _ _ h => h)
  · intro inp work out h
    simpa only [unboxed_length, unboxedWords] using h
  · exact Nat.mul_le_mul_right _ hlen

end JointThermoComplexity.Complexity.DenseFourTemplatePacket

#print axioms JointThermoComplexity.Complexity.DenseFourTemplatePacket.map_lookup
#print axioms JointThermoComplexity.Complexity.DenseFourTemplatePacket.boxed_hoareTime
#print axioms JointThermoComplexity.Complexity.DenseFourTemplatePacket.unboxed_hoareTime
