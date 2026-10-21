module
public import proofs.JointThermoComplexity.Complexity.MotifDirectionState
public import proofs.JointThermoComplexity.Complexity.MotifBufferMeta

set_option autoImplicit false
@[expose] public section

/-! A precise direction-pass frame retains the separate species mask while two heads and one address advance. -/

namespace JointThermoComplexity.Complexity.MotifDirectionFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts MotifDirectionState MonomialPorts

def Unchanged (m : ℕ) (work work' : Fin (m + 15) → Tape) : Prop :=
  ∀ j, j ≠ buffer m 1 → j ≠ buffer m 2 → j ≠ species (m + 1) → work' j = work j

theorem Unchanged.box {m : ℕ} {work work' : Fin (m + 15) → Tape} (h : Unchanged m work work') :
    BoxState.Unchanged m work work' := fun j _ ha hb _ hs => h j ha hb hs

theorem metadata (m : ℕ) (input : List Bool) (work work' : Fin (m + 15) → Tape)
    (hw : Unchanged m work work') : MotifBufferMeta.State m input work → MotifBufferMeta.State m input work' := by
  rintro ⟨hk, hr⟩
  exact ⟨BoxPins.frame m input work work' hw.box hk, BoxRegisters.frame m input work work' hw.box hr⟩

theorem species_mask (m : ℕ) (bits : List Bool) (work work' : Fin (m + 15) → Tape)
    (hw : Unchanged m work work') : BoxBufferState.Stored bits (work (buffer m 0)) →
      BoxBufferState.Stored bits (work' (buffer m 0)) := by
  have hne₁ : buffer m 0 ≠ buffer m 1 := by intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 3 at hv; omega
  have hne₂ : buffer m 0 ≠ buffer m 2 := by intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 4 at hv; omega
  have hne₃ : buffer m 0 ≠ species (m + 1) := by intro he; have hv := congrArg Fin.val he; change (2 : ℕ) = 7 at hv; omega
  rw [hw _ hne₁ hne₂ hne₃]
  exact id

theorem map_state (m L idx : ℕ) (mask flags : List Bool) (i : ℕ)
    (R S : (Fin (m + 15) → Tape) → Prop) (work : Fin (m + 15) → Tape)
    (hr : R work → S work) (hp : State m L idx mask flags i R work) : State m L idx mask flags i S work := by
  rcases hp with ⟨⟨hs, hz, hi, hb, hR⟩, hm, hf⟩
  exact ⟨⟨hs, hz, hi, hb, hr hR⟩, hm, hf⟩

theorem advance_unchanged (m : ℕ) (work : Fin (m + 15) → Tape) :
    Unchanged m work (WorkHeadsAdvance.advance (MotifDirectionState.ports m) work) := by
  intro j ha hb _
  simp [WorkHeadsAdvance.advance, MotifDirectionState.ports, ha, hb]

theorem advance_state (m L idx : ℕ) (mask flags : List Bool) (i : ℕ)
    (hm : mask.length ≤ L) (hf : flags.length ≤ L) (him : i < mask.length) (hif : i < flags.length)
    (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work')
    (work : Fin (m + 15) → Tape) (hp : State m L idx mask flags i R work) :
    State m L idx mask flags (i + 1) R (WorkHeadsAdvance.advance (MotifDirectionState.ports m) work) := by
  have hp₀ := map_state m L idx mask flags i R (fun _ => True) work (fun _ => trivial) hp
  have h₀ := MotifDirectionState.advance_state m L idx mask flags i hm hf him hif
    (fun _ => True) (fun _ _ _ _ => trivial) work hp₀
  exact map_state m L idx mask flags (i + 1) (fun _ => True) R _
    (fun _ => hR work _ (advance_unchanged m work) hp.1.2.2.2.2) h₀

theorem hoareTime (m L idx : ℕ) (mask flags : List Bool) (i : ℕ)
    (hm : mask.length ≤ L) (hf : flags.length ≤ L) (him : i < mask.length) (hif : i < flags.length)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (MotifDirectionState.machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ State m L idx mask flags i R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ State m L idx mask flags (i + 1) R work) 1 := by
  have hs := WorkHeadsAdvance.hoareTime (MotifDirectionState.ports m) before input emitted
    (fun work _ => State m L idx mask flags i R work) (fun work _ => State m L idx mask flags (i + 1) R work)
    (fun work _ hp => advance_state m L idx mask flags i hm hf him hif R hR work hp)
  exact hs.consequence (fun _ _ _ ⟨hc, hp⟩ => ⟨hc, hp.1.1, hp⟩) (fun _ _ _ ⟨hc, _, hp⟩ => ⟨hc, hp⟩) le_rfl

end JointThermoComplexity.Complexity.MotifDirectionFrame

#print axioms JointThermoComplexity.Complexity.MotifDirectionFrame.metadata
#print axioms JointThermoComplexity.Complexity.MotifDirectionFrame.species_mask
#print axioms JointThermoComplexity.Complexity.MotifDirectionFrame.hoareTime
