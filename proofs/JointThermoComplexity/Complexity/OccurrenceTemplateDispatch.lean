module
public import proofs.JointThermoComplexity.Complexity.OccurrenceDispatchControl

set_option autoImplicit false
@[expose] public section

/-! One actual finite branch machine chooses among a pre-input family of
continuations. The static port list bounds the alternatives; the selected
numeric count does not create a new input-dependent machine. -/

namespace JointThermoComplexity.Complexity.OccurrenceTemplateDispatch
open _root_.Complexity _root_.Complexity.TM HeaderAt
open BoundedOccurrenceMachine OccurrenceDispatchControl
variable {w : ℕ}

def walk : List (Port w) → Fin (w + 1) → (ℕ → TM (w + 1)) → TM (w + 1) → ℕ → TM (w + 1)
  | [], ending, programs, invalid, start =>
    WorkSymbolBranch.machine Γ.one ending invalid (programs start)
  | p :: slots, ending, programs, invalid, start =>
    WorkSymbolBranch.machine Γ.one p.2 (walk slots ending programs invalid (start + 1)) (programs start)

def machine (slots : List (Port w)) (ending flag : Fin (w + 1))
    (programs : ℕ → TM (w + 1)) (invalid : TM (w + 1)) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one flag (walk slots ending programs invalid 0) invalid

def selected (programs : ℕ → TM (w + 1)) (invalid : TM (w + 1)) : Option ℕ → TM (w + 1)
  | none => invalid
  | some m => programs m

theorem walk_position_hoareTime (slots : List (Port w)) (ending : Fin (w + 1))
    (programs : ℕ → TM (w + 1)) (invalid : TM (w + 1)) (start m : ℕ)
    (before input emitted before' input' emitted' : List Bool)
    (P Q : (Fin (w + 1) → Tape) → Prop) (B : ℕ)
    (h : (programs (start + m)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) B) :
    (walk slots ending programs invalid start).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work ∧ Position slots ending m work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) (B + slots.length + 2) := by
  induction slots generalizing start m with
  | nil =>
    cases m with
    | zero =>
      have hb := WorkSymbolBranch.no_hoareTime Γ.one ending invalid (programs start)
        before input emitted before' input' emitted' P Q B h
      apply hb.consequence
      · rintro inp work out ⟨hc, hp, hm⟩
        exact ⟨⟨hc, hp⟩, by rw [hm]; decide⟩
      · exact fun _ _ _ hp => hp
      · simp
    | succ m =>
      rintro inp work out ⟨_, _, hm⟩
      exact hm.elim
  | cons p slots ih =>
    cases m with
    | zero =>
      have hb := WorkSymbolBranch.no_hoareTime Γ.one p.2
        (walk slots ending programs invalid (start + 1)) (programs start)
        before input emitted before' input' emitted' P Q B h
      apply hb.consequence
      · rintro inp work out ⟨hc, hp, hm⟩
        exact ⟨⟨hc, hp⟩, by rw [hm]; decide⟩
      · exact fun _ _ _ hp => hp
      · simp only [List.length_cons]; omega
    | succ m =>
      have he : start + 1 + m = start + (m + 1) := by omega
      have hp : (programs (start + 1 + m)).HoareTime
          (fun inp work out => Cursor before input emitted inp work out ∧ P work)
          (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) B := by
        rw [he]
        exact h
      have hi := ih (start + 1) m hp
      have hb := WorkSymbolBranch.yes_hoareTime Γ.one p.2
        (walk slots ending programs invalid (start + 1)) (programs start)
        before input emitted before' input' emitted'
        (fun work => P work ∧ Position slots ending m work) Q (B + slots.length + 2) hi
      apply hb.consequence
      · rintro inp work out ⟨hc, hp, hm, ht⟩
        exact ⟨⟨hc, hp, ht⟩, hm⟩
      · exact fun _ _ _ hp => hp
      · simp only [List.length_cons]; omega

theorem walk_overflow_hoareTime (slots : List (Port w)) (ending : Fin (w + 1))
    (programs : ℕ → TM (w + 1)) (invalid : TM (w + 1)) (start : ℕ)
    (before input emitted before' input' emitted' : List Bool)
    (P Q : (Fin (w + 1) → Tape) → Prop) (B : ℕ)
    (h : invalid.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) B) :
    (walk slots ending programs invalid start).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work ∧ Overflow slots ending work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) (B + slots.length + 1) := by
  induction slots generalizing start with
  | nil =>
    have hb := WorkSymbolBranch.yes_hoareTime Γ.one ending invalid (programs start)
      before input emitted before' input' emitted' P Q B h
    apply hb.consequence
    · rintro inp work out ⟨hc, hp, hm⟩
      exact ⟨⟨hc, hp⟩, hm⟩
    · exact fun _ _ _ hp => hp
    · simp
  | cons p slots ih =>
    have hi := ih (start + 1)
    have hb := WorkSymbolBranch.yes_hoareTime Γ.one p.2
      (walk slots ending programs invalid (start + 1)) (programs start)
      before input emitted before' input' emitted'
      (fun work => P work ∧ Overflow slots ending work) Q (B + slots.length + 1) hi
    apply hb.consequence
    · rintro inp work out ⟨hc, hp, hm, ht⟩
      exact ⟨⟨hc, hp, ht⟩, hm⟩
    · exact fun _ _ _ hp => hp
    · simp only [List.length_cons]; omega

theorem hoareTime (slots : List (Port w)) (ending flag : Fin (w + 1))
    (programs : ℕ → TM (w + 1)) (invalid : TM (w + 1)) (choice : Option ℕ)
    (before input emitted before' input' emitted' : List Bool)
    (P Q : (Fin (w + 1) → Tape) → Prop) (B : ℕ)
    (h : (selected programs invalid choice).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) B) :
    (machine slots ending flag programs invalid).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work ∧ Route slots ending flag choice work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) (B + slots.length + 3) := by
  cases choice with
  | none =>
    have hi := walk_overflow_hoareTime slots ending programs invalid 0
      before input emitted before' input' emitted' P Q B h
    have hy := WorkSymbolBranch.yes_hoareTime Γ.one flag (walk slots ending programs invalid 0) invalid
      before input emitted before' input' emitted'
      (fun work => P work ∧ Overflow slots ending work) Q (B + slots.length + 1) hi
    have hn := WorkSymbolBranch.no_hoareTime Γ.one flag (walk slots ending programs invalid 0) invalid
      before input emitted before' input' emitted' P Q B h
    rintro inp work out ⟨hc, hp, hr⟩
    by_cases hf : (work flag).read = Γ.one
    · have ho : Overflow slots ending work := hr.resolve_left (fun hn => hn hf)
      obtain ⟨d, t, ht, hd, hh, hq⟩ := hy inp work out ⟨⟨hc, hp, ho⟩, hf⟩
      exact ⟨d, t, by omega, hd, hh, hq⟩
    · obtain ⟨d, t, ht, hd, hh, hq⟩ := hn inp work out ⟨⟨hc, hp⟩, hf⟩
      exact ⟨d, t, by omega, hd, hh, hq⟩
  | some m =>
    have hp : (programs (0 + m)).HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ P work)
        (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) B := by
      simpa only [selected, Nat.zero_add] using h
    have hi := walk_position_hoareTime slots ending programs invalid 0 m
      before input emitted before' input' emitted' P Q B hp
    have hy := WorkSymbolBranch.yes_hoareTime Γ.one flag (walk slots ending programs invalid 0) invalid
      before input emitted before' input' emitted'
      (fun work => P work ∧ Position slots ending m work) Q (B + slots.length + 2) hi
    apply hy.consequence
    · rintro inp work out ⟨hc, hp, hf, hm⟩
      exact ⟨⟨hc, hp, hm⟩, hf⟩
    · exact fun _ _ _ hp => hp
    · omega

theorem loaded_hoareTime (slots : List (Port w)) (ending flag : Fin (w + 1))
    (programs : ℕ → TM (w + 1)) (invalid : TM (w + 1)) (raw : List Bool)
    (before input emitted before' input' emitted' : List Bool)
    (P Q : (Fin (w + 1) → Tape) → Prop) (B : ℕ)
    (h : (selected programs invalid (OccurrenceDispatchControl.choice slots.length raw)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) B) :
    (machine slots ending flag programs invalid).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ P work ∧ Loaded slots ending flag raw work)
      (fun inp work out => Cursor before' input' emitted' inp work out ∧ Q work) (B + slots.length + 3) := by
  apply (hoareTime slots ending flag programs invalid (OccurrenceDispatchControl.choice slots.length raw)
    before input emitted before' input' emitted' P Q B h).consequence
  · rintro inp work out ⟨hc, hp, hl⟩
    exact ⟨hc, hp, loaded_route slots ending flag raw work hl⟩
  · exact fun _ _ _ hp => hp
  · exact le_rfl

end JointThermoComplexity.Complexity.OccurrenceTemplateDispatch

#print axioms JointThermoComplexity.Complexity.OccurrenceTemplateDispatch.machine
#print axioms JointThermoComplexity.Complexity.OccurrenceTemplateDispatch.hoareTime
#print axioms JointThermoComplexity.Complexity.OccurrenceTemplateDispatch.loaded_hoareTime
