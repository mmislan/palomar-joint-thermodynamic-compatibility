module
public import proofs.JointThermoComplexity.Complexity.MotifBufferPorts
public import proofs.JointThermoComplexity.Complexity.WorkHeadsAdvance

set_option autoImplicit false
@[expose] public section

/-! Synchronized cursors over the retained reaction mask and common orientations. -/

namespace JointThermoComplexity.Complexity.MotifDirectionState
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts BoxBufferState PowerPorts MonomialPorts ReactionPorts

structure At (bits : List Bool) (i : ℕ) (t : Tape) : Prop where
  content : t.HasBinaryContent bits
  zero : t.cells 0 = Γ.start
  head : t.head = i + 1

theorem At.read {bits : List Bool} {i : ℕ} {t : Tape} (h : At bits i t) (hi : i < bits.length) :
    t.read = Γ.ofBool bits[i] := by rw [Tape.read, h.head, h.content.1 i hi]

theorem At.advance {bits : List Bool} {i : ℕ} {t : Tape} (h : At bits i t) : At bits (i + 1) (t.move .right) :=
  ⟨h.content, h.zero, by change t.head + 1 = i + 1 + 1; rw [h.head]⟩

theorem At.reusable {bits : List Bool} {i L : ℕ} {t : Tape} (h : At bits i t)
    (hlen : bits.length ≤ 4 * L) (hi : i ≤ bits.length) : Reusable L t :=
  ⟨bits, hlen, h.content, h.zero, by rw [h.head]; omega⟩

theorem At.stored {bits : List Bool} {t : Tape} (h : At bits bits.length t) : Stored bits t :=
  ⟨⟨h.head, h.content⟩, h.zero⟩

def State (m L idx : ℕ) (mask flags : List Bool) (i : ℕ)
    (R : (Fin (m + 15) → Tape) → Prop) (work : Fin (m + 15) → Tape) : Prop :=
  BoxState.Ready m L idx R work ∧ At mask i (work (buffer m 1)) ∧ At flags i (work (buffer m 2))

def ports (m : ℕ) : List (Fin (m + 15)) := [buffer m 1, buffer m 2]

def machine (m : ℕ) : TM (m + 15) := WorkHeadsAdvance.machine (ports m)

theorem advance_state (m L idx : ℕ) (mask flags : List Bool) (i : ℕ)
    (hm : mask.length ≤ L) (hf : flags.length ≤ L) (him : i < mask.length) (hif : i < flags.length)
    (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', BoxState.Unchanged m work work' → R work → R work')
    (work : Fin (m + 15) → Tape) (hp : State m L idx mask flags i R work) :
    State m L idx mask flags (i + 1) R (WorkHeadsAdvance.advance (ports m) work) := by
  let work' := WorkHeadsAdvance.advance (ports m) work
  have hstay (j : Fin (m + 15)) (hj : j.val ≠ 3 ∧ j.val ≠ 4) : work' j = work j := by
    have hne₁ : j ≠ buffer m 1 := by intro he; have hv := congrArg Fin.val he; exact hj.1 hv
    have hne₂ : j ≠ buffer m 2 := by intro he; have hv := congrArg Fin.val he; exact hj.2 hv
    simp [work', WorkHeadsAdvance.advance, ports, hne₁, hne₂]
  have hmask : At mask (i + 1) (work' (buffer m 1)) := by
    simpa [work', WorkHeadsAdvance.advance, ports] using hp.2.1.advance
  have hflags : At flags (i + 1) (work' (buffer m 2)) := by
    simpa [work', WorkHeadsAdvance.advance, ports] using hp.2.2.advance
  have hu : BoxState.Unchanged m work work' := by
    intro j _ ha hb _ _
    have hne₁ : j ≠ buffer m 1 := ha
    have hne₂ : j ≠ buffer m 2 := hb
    have hne : j ∉ ports m := by simpa [ports] using And.intro hne₁ hne₂
    simp only [work', WorkHeadsAdvance.advance, hne, ↓reduceIte]
  refine ⟨⟨WorkHeadsAdvance.parked (ports m) work hp.1.1, ?_, ?_, ?_, hR work work' hu hp.1.2.2.2.2⟩, hmask, hflags⟩
  · change BinaryIncrementRun.Register 0 (work' (scratch (m + 2)))
    rw [hstay (scratch (m + 2)) (by change (5 : ℕ) ≠ 3 ∧ 5 ≠ 4; omega)]
    exact hp.1.2.1
  · change IsReg idx (work' (species (m + 1)))
    rw [hstay (species (m + 1)) (by change (7 : ℕ) ≠ 3 ∧ 7 ≠ 4; omega)]
    exact hp.1.2.2.1
  · change BoxState.Buffers m L work'
    refine ⟨?_, hmask.reusable (by omega) (by omega), hflags.reusable (by omega) (by omega), ?_⟩
    · rw [hstay (next (m + 2)) (by change (2 : ℕ) ≠ 3 ∧ 2 ≠ 4; omega)]
      exact hp.1.2.2.2.1.1
    · rw [hstay (saved m) (by change (8 : ℕ) ≠ 3 ∧ 8 ≠ 4; omega)]
      exact hp.1.2.2.2.1.2.2.2

theorem hoareTime (m L idx : ℕ) (mask flags : List Bool) (i : ℕ)
    (hm : mask.length ≤ L) (hf : flags.length ≤ L) (him : i < mask.length) (hif : i < flags.length)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', BoxState.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ State m L idx mask flags i R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ State m L idx mask flags (i + 1) R work) 1 := by
  have hs := WorkHeadsAdvance.hoareTime (ports m) before input emitted
    (fun work _ => State m L idx mask flags i R work) (fun work _ => State m L idx mask flags (i + 1) R work)
    (fun work _ hp => advance_state m L idx mask flags i hm hf him hif R hR work hp)
  exact hs.consequence (fun _ _ _ ⟨hc, hp⟩ => ⟨hc, hp.1.1, hp⟩) (fun _ _ _ ⟨hc, _, hp⟩ => ⟨hc, hp⟩) le_rfl

end JointThermoComplexity.Complexity.MotifDirectionState

#print axioms JointThermoComplexity.Complexity.MotifDirectionState.At.read
#print axioms JointThermoComplexity.Complexity.MotifDirectionState.advance_state
#print axioms JointThermoComplexity.Complexity.MotifDirectionState.hoareTime
