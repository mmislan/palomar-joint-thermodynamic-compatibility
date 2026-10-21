module
public import proofs.JointThermoComplexity.Complexity.SparseTermOffsetControl
public import proofs.JointThermoComplexity.Complexity.BinaryConstantAdd

set_option autoImplicit false
@[expose] public section

/-! A finite marker dispatch adds the exact normalized row count in binary. -/

namespace JointThermoComplexity.Complexity.NormalizedCountDispatch
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementFramed
variable {w : ℕ}

def added : Option ℕ → ℕ
  | none => 0
  | some m => 2 ^ m

def programs (idx : Fin (w + 1)) (m : ℕ) : TM (w + 1) := BinaryConstantAdd.machine (2 ^ m) idx

def machine (slots : List (BoundedOccurrenceMachine.Port w)) (ending flag idx : Fin (w + 1)) : TM (w + 1) :=
  OccurrenceTemplateDispatch.machine slots ending flag (programs idx) (emitBitsTM [])

theorem selected_eq (idx : Fin (w + 1)) (choice : Option ℕ) :
    OccurrenceTemplateDispatch.selected (programs idx) (emitBitsTM []) choice =
      BinaryConstantAdd.machine (added choice) idx := by cases choice <;> rfl

theorem added_le (raw : List Bool) : added (OccurrenceDispatchControl.choice 4 raw) ≤ 16 := by
  cases h : OccurrenceDispatchControl.choice 4 raw with
  | none => simp only [added]; omega
  | some m =>
    have hm := OffsetTemplateDispatch.choice_le 4 raw m h
    simpa only [added] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hm

theorem hoareTime (slots : List (BoundedOccurrenceMachine.Port w)) (ending flag idx : Fin (w + 1))
    (hslots : slots.length = 4) (raw : List Bool) (N C : ℕ) (hN : N.bits.length ≤ C)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable idx R) :
    (machine slots ending flag idx).HoareTime
      (fun inp work out => Logical idx N before input emitted R inp work out ∧
        BoundedOccurrenceMachine.Loaded slots ending flag raw work)
      (Logical idx (N + added (OccurrenceDispatchControl.choice 4 raw)) before input emitted R)
      (32 * C + 599) := by
  let k := added (OccurrenceDispatchControl.choice 4 raw)
  have hk : k ≤ 16 := added_le raw
  have hp := BinaryConstantAdd.hoareTime k idx N before input emitted R hR
  have hbound : k * (2 * N.bits.length + 2 * k + 5) ≤ 32 * C + 592 := by
    calc
      _ ≤ 16 * (2 * C + 2 * 16 + 5) := Nat.mul_le_mul hk (by omega)
      _ = _ := by omega
  have hs : (OccurrenceTemplateDispatch.selected (programs idx) (emitBitsTM [])
      (OccurrenceDispatchControl.choice slots.length raw)).HoareTime
      (Logical idx N before input emitted R) (Logical idx (N + k) before input emitted R) (32 * C + 592) := by
    rw [hslots, selected_eq]
    exact hp.mono_bound hbound
  have hd := OccurrenceTemplateDispatch.loaded_hoareTime slots ending flag (programs idx) (emitBitsTM []) raw
    before input emitted before input emitted
    (fun work => (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register N (work idx) ∧ R work)
    (fun work => (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register (N + k) (work idx) ∧ R work)
    (32 * C + 592) hs
  apply hd.consequence
  · rintro inp work out ⟨⟨hc, hs, hn, hr⟩, hl⟩
    exact ⟨hc, ⟨hs, hn, hr⟩, hl⟩
  · exact fun _ _ _ hp => hp
  · rw [hslots]

end JointThermoComplexity.Complexity.NormalizedCountDispatch

#print axioms JointThermoComplexity.Complexity.NormalizedCountDispatch.machine
#print axioms JointThermoComplexity.Complexity.NormalizedCountDispatch.hoareTime
