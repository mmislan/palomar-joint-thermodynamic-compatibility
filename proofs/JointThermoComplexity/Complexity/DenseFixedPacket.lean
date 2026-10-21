module
public import proofs.JointThermoComplexity.Complexity.DenseFixedRawStep

set_option autoImplicit false
@[expose] public section

/-! The two precompiled initial rows share the same returned reference bank. -/

namespace JointThermoComplexity.Complexity.DenseFixedPacket
open _root_.Complexity _root_.Complexity.TM HeaderAt
open DenseFixedComplexOriginal DenseComplexOriginal DenseFixedRawStep

def external (boxed offset : Bool) : TM 64 :=
  if boxed then DenseFixedExternalPower.boxedMachine else DenseFixedExternalPower.unboxedMachine (offsetPower offset)
def externalBound (boxed offset : Bool) (n : ℕ) : ℕ :=
  if boxed then DenseFixedExternalPower.boxedBound n else DenseFixedExternalPower.unboxedBound n (offsetPower offset)
def rowMachine (boxed right offset : Bool) : TM 64 := DenseFixedRawStep.machine boxed right offset (external boxed offset)
def rowWord (boxed right offset : Bool) (n N U : ℕ) : List Bool :=
  if boxed then DenseFixedRawRecord.word true right offset U N (initialVertex offset N) n (fun _ => 0)
  else DenseFixedRawRecord.word false right offset U N (initialVertex offset N) ((n + n) + 1) (Fin.cons (offsetPower offset) (fun _ => 0))
def rowBound (boxed right offset : Bool) (n N B : ℕ) : ℕ := DenseFixedRawStep.timeBound right N B (externalBound boxed offset n)
def machine (boxed right : Bool) : TM 64 := seqTM (rowMachine boxed right false) (rowMachine boxed right true)
def word (boxed right : Bool) (n N U : ℕ) : List Bool := rowWord boxed right false n N U ++ rowWord boxed right true n N U
def timeBound (boxed right : Bool) (n N B : ℕ) : ℕ := rowBound boxed right false n N B + 1 + rowBound boxed right true n N B

theorem row_hoareTime (boxed right offset : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N U B u : ℕ)
    (hU : U.bits.length ≤ B) (hbase : N + 2 ≤ B) (hu : u ≤ N + 1)
    (R : (Fin 64 → Tape) → Prop) (hR : DenseRowFrame.Stable R) (before input emitted : List Bool) :
    (rowMachine boxed right offset).HoareTime (At (initialVertex offset N).val u m hm values n N U before input emitted R)
      (At ((initialVertex offset N).val + 1) (vertex true (initialVertex offset N)).val m hm values n N U
        before input (emitted ++ rowWord boxed right offset n N U) R) (rowBound boxed right offset n N B) := by
  have hi : (initialVertex offset N).val.bits.length ≤ B := (BoundedUnaryControl.bits_le _).trans (by
    have hv := (initialVertex offset N).isLt; omega)
  have hnext : (vertex true (initialVertex offset N)).val.bits.length ≤ B := (BoundedUnaryControl.bits_le _).trans (by
    have hv := (vertex true (initialVertex offset N)).isLt; omega)
  have hend : (N + 1).bits.length ≤ B := (BoundedUnaryControl.bits_le _).trans (by omega)
  have hub : u.bits.length ≤ B := (BoundedUnaryControl.bits_le _).trans (by omega)
  cases boxed with
  | false =>
    exact DenseFixedRawStep.hoareTime false right offset m hm values n N U B (initialVertex offset N) u ((n + n) + 1)
      (Fin.cons (offsetPower offset) (fun _ => 0)) _ _ (DenseFixedExternalPower.unboxed_emits m hm values n (offsetPower offset))
      hU hi hnext hend hub R hR before input emitted
  | true =>
    exact DenseFixedRawStep.hoareTime true right offset m hm values n N U B (initialVertex offset N) u n
      (fun _ => 0) _ _ (DenseFixedExternalPower.boxed_emits m hm values n)
      hU hi hnext hend hub R hR before input emitted

theorem hoareTime (boxed right : Bool) (m : ℕ) (hm : m ≤ 4) (values : Fin 64 → ℕ) (n N U B u : ℕ)
    (hU : U.bits.length ≤ B) (hbase : N + 2 ≤ B) (hu : u ≤ N + 1)
    (R : (Fin 64 → Tape) → Prop) (hR : DenseRowFrame.Stable R) (before input emitted : List Bool) :
    (machine boxed right).HoareTime (At 0 u m hm values n N U before input emitted R)
      (At 2 (vertex true (initialVertex true N)).val m hm values n N U before input
        (emitted ++ word boxed right n N U) R) (timeBound boxed right n N B) := by
  have h1 := row_hoareTime boxed right false m hm values n N U B u hU hbase hu R hR before input emitted
  have h2 := row_hoareTime boxed right true m hm values n N U B (vertex true (initialVertex false N)).val hU hbase
    (by have hv := (vertex true (initialVertex false N)).isLt; omega) R hR before input
    (emitted ++ rowWord boxed right false n N U)
  have hh := seqTM_hoareTime _ _ h1 (by
    intro inp work out h
    obtain ⟨hi, hw, ho⟩ := h.1.phase
    rw [hi, hw, ho]
    exact h) h2
  apply hh.consequence (fun _ _ _ h => h)
  · intro inp work out h
    have hcurrent : (initialVertex true N).val + 1 = 2 := by simp [initialVertex]
    rw [hcurrent] at h
    simpa only [word, List.append_assoc] using h
  · exact le_rfl

end JointThermoComplexity.Complexity.DenseFixedPacket

#print axioms JointThermoComplexity.Complexity.DenseFixedPacket.hoareTime
