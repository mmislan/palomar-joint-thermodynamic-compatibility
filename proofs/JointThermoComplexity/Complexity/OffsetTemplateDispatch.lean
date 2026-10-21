module
public import proofs.JointThermoComplexity.Complexity.OffsetTemplateData
public import proofs.JointThermoComplexity.Complexity.OccurrenceTemplateDispatch

set_option autoImplicit false
@[expose] public section

/-! One finite marker-dispatched offset program for all raw occurrence
fields. Missing/overflow fields take the empty continuation; valid fields
select the exact cube/orthant template for their occurrence count. -/

namespace JointThermoComplexity.Complexity.OffsetTemplateDispatch
open _root_.Complexity _root_.Complexity.TM HeaderAt
open BoundedOccurrenceMachine
open OffsetContribution (Separate Stable)
open OffsetTemplateProgram (Inv Fields)
variable {w : ℕ}

def added (boxed negative : Bool) (v : ℕ) : Option ℕ → ℕ
  | none => 0
  | some m => OffsetTemplateProgram.total negative v (OffsetTemplateData.template boxed m)

def programs (boxed : Bool) (idx sign adjusted acc aux : Fin w) (m : ℕ) : TM (w + 1) :=
  OffsetTemplateProgram.machine (OffsetTemplateData.template boxed m) idx sign adjusted acc aux

def machine (boxed : Bool) (slots : List (Port w)) (ending flag : Fin (w + 1))
    (idx sign adjusted acc aux : Fin w) : TM (w + 1) :=
  OccurrenceTemplateDispatch.machine slots ending flag (programs boxed idx sign adjusted acc aux) (emitBitsTM [])

theorem bound_le_sixteen (N B C : ℕ) (hN : N ≤ 16) :
    OffsetTemplateProgram.bound N B C ≤ OffsetTemplateProgram.bound 16 B C := by
  have hp := Nat.mul_le_mul_right (B + 2609) hN
  have hi : 13 * (C + N * (B + 2609)) + 54 * B + 138381 ≤
      13 * (C + 16 * (B + 2609)) + 54 * B + 138381 := by omega
  exact Nat.mul_le_mul hN hi

theorem choice_le (capacity : ℕ) (raw : List Bool) (m : ℕ)
    (h : OccurrenceDispatchControl.choice capacity raw = some m) : m ≤ capacity := by
  unfold OccurrenceDispatchControl.choice at h
  dsimp only at h
  split at h
  · have hm := Option.some.inj h
    rw [← hm]
    exact BoundedOccurrenceControl.values_length capacity raw
  · contradiction

theorem selected_hoareTime (boxed negative : Bool) (v A C : ℕ) (choice : Option ℕ)
    (hchoice : ∀ m, choice = some m → m ≤ 4)
    (idx sign adjusted acc aux : Fin w) (sep : Separate idx sign adjusted acc aux)
    (hA : A.bits.length ≤ C) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable adjusted acc aux R) :
    (OccurrenceTemplateDispatch.selected (programs boxed idx sign adjusted acc aux) (emitBitsTM []) choice).HoareTime
      (Inv idx sign adjusted acc aux v A negative before input emitted R)
      (Inv idx sign adjusted acc aux v (A + added boxed negative v choice) negative before input emitted R)
      (OffsetTemplateProgram.bound 16 v.bits.length C) := by
  cases choice with
  | none =>
    have h := FixedOutput.hoareTime [] before input emitted (Fields idx sign adjusted acc aux v A negative R)
    apply h.consequence (fun _ _ _ hp => hp)
    · intro inp work out hp
      simpa only [OffsetTemplateProgram.Inv, added, List.append_nil, Nat.add_zero] using hp
    · simp only [List.length_nil]
      omega
  | some m =>
    have hm := hchoice m rfl
    have h := OffsetTemplateProgram.hoareTime (OffsetTemplateData.template boxed m) negative v A C
      idx sign adjusted acc aux sep (OffsetTemplateData.template_bounded boxed m hm) hA before input emitted R hR
    apply h.consequence (fun _ _ _ hp => hp)
    · intro inp work out hp
      simpa only [added] using hp
    · exact bound_le_sixteen _ _ _ (OffsetTemplateData.template_length boxed m hm)

theorem hoareTime (boxed negative : Bool) (v A C : ℕ) (slots : List (Port w))
    (ending flag : Fin (w + 1)) (hslots : slots.length = 4) (raw : List Bool)
    (idx sign adjusted acc aux : Fin w) (sep : Separate idx sign adjusted acc aux)
    (hA : A.bits.length ≤ C) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable adjusted acc aux R) :
    (machine boxed slots ending flag idx sign adjusted acc aux).HoareTime
      (fun inp work out => Inv idx sign adjusted acc aux v A negative before input emitted R inp work out ∧
        Loaded slots ending flag raw work)
      (Inv idx sign adjusted acc aux v
        (A + added boxed negative v (OccurrenceDispatchControl.choice slots.length raw)) negative before input emitted R)
      (OffsetTemplateProgram.bound 16 v.bits.length C + 7) := by
  have hcap : ∀ m, OccurrenceDispatchControl.choice slots.length raw = some m → m ≤ 4 := by
    intro m hm
    simpa only [hslots] using choice_le slots.length raw m hm
  have hs := selected_hoareTime boxed negative v A C (OccurrenceDispatchControl.choice slots.length raw)
    hcap idx sign adjusted acc aux sep hA before input emitted R hR
  have h := OccurrenceTemplateDispatch.loaded_hoareTime slots ending flag
    (programs boxed idx sign adjusted acc aux) (emitBitsTM []) raw before input emitted before input emitted
    (fun work => (∀ j, Parked (work j)) ∧ Fields idx sign adjusted acc aux v A negative R work)
    (fun work => (∀ j, Parked (work j)) ∧ Fields idx sign adjusted acc aux v
      (A + added boxed negative v (OccurrenceDispatchControl.choice slots.length raw)) negative R work)
    (OffsetTemplateProgram.bound 16 v.bits.length C) hs
  apply h.consequence
  · rintro inp work out ⟨hp, hl⟩
    exact ⟨hp.1, hp.2, hl⟩
  · exact fun _ _ _ hp => hp
  · rw [hslots]

theorem code_hoareTime {n : ℕ} (boxed negative : Bool) (v A C : ℕ) (slots : List (Port w))
    (ending flag : Fin (w + 1)) (hslots : slots.length = 4) (vs : List (Fin n)) (suffix : List Bool)
    (hvs : vs.length ≤ 4) (idx sign adjusted acc aux : Fin w) (sep : Separate idx sign adjusted acc aux)
    (hA : A.bits.length ≤ C) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable adjusted acc aux R) :
    (machine boxed slots ending flag idx sign adjusted acc aux).HoareTime
      (fun inp work out => Inv idx sign adjusted acc aux v A negative before input emitted R inp work out ∧
        Loaded slots ending flag (SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) work)
      (Inv idx sign adjusted acc aux v
        (A + OffsetTemplateProgram.total negative v (OffsetTemplateData.template boxed vs.length))
        negative before input emitted R)
      (OffsetTemplateProgram.bound 16 v.bits.length C + 7) := by
  have hcap : vs.length ≤ slots.length := by omega
  simpa only [OccurrenceDispatchControl.choice_code vs suffix slots.length hcap, added] using
    hoareTime boxed negative v A C slots ending flag hslots
      (SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix)
      idx sign adjusted acc aux sep hA before input emitted R hR

end JointThermoComplexity.Complexity.OffsetTemplateDispatch

#print axioms JointThermoComplexity.Complexity.OffsetTemplateDispatch.machine
#print axioms JointThermoComplexity.Complexity.OffsetTemplateDispatch.hoareTime
#print axioms JointThermoComplexity.Complexity.OffsetTemplateDispatch.code_hoareTime
