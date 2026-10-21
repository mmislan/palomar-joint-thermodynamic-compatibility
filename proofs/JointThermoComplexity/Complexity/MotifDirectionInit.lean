module
public import proofs.JointThermoComplexity.Complexity.MotifBufferRewind
public import proofs.JointThermoComplexity.Complexity.MotifDirectionFrame

set_option autoImplicit false
@[expose] public section

/-! Rewind the actual reaction mask and common orientation vectors into synchronized position zero. -/

namespace JointThermoComplexity.Complexity.MotifDirectionInit
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts MotifDirectionState MotifDirectionFrame BoxBufferState

def machine (m : ℕ) : TM (m + 15) := seqTM (rewindWorkTM (buffer m 1)) (rewindWorkTM (buffer m 2))

theorem hoareTime (m L idx : ℕ) (mask flags : List Bool) (hm : mask.length ≤ L) (hf : flags.length ≤ L)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ BoxState.Ready m L idx R work ∧
        Stored mask (work (buffer m 1)) ∧ Stored flags (work (buffer m 2)))
      (fun inp work out => Cursor before input emitted inp work out ∧ State m L idx mask flags 0 R work) (2 * L + 7) := by
  have hne : buffer m 1 ≠ buffer m 2 := by intro he; have hv := congrArg Fin.val he; change (3 : ℕ) = 4 at hv; omega
  let P : (Fin (m + 15) → Tape) → Prop := fun work => R work ∧ Stored flags (work (buffer m 2))
  have hP : ∀ work work', (∀ j, j ≠ buffer m 1 → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hr, hs⟩
    exact ⟨hR work work' (fun j hm _ _ => hw j hm) hr, by rw [hw _ hne.symm]; exact hs⟩
  let Q : (Fin (m + 15) → Tape) → Prop := fun work => R work ∧ At mask 0 (work (buffer m 1))
  have hQ : ∀ work work', (∀ j, j ≠ buffer m 2 → work' j = work j) → Q work → Q work' := by
    rintro work work' hw ⟨hr, hs⟩
    exact ⟨hR work work' (fun j _ hf _ => hw j hf) hr, by rw [hw _ hne]; exact hs⟩
  have hmask := MotifBufferRewind.hoareTime m L idx 1 mask before input emitted hm P hP
  have hflags := MotifBufferRewind.hoareTime m L idx 2 flags before input emitted hf Q hQ
  have hs := seqTM_hoareTime (rewindWorkTM (buffer m 1)) (rewindWorkTM (buffer m 2)) hmask (by
    rintro inp work out ⟨hc, ⟨hsa, hz, hi, hb, hr, hstored⟩, hat⟩
    obtain ⟨hip, hw, ho⟩ := hc.phase
    rw [hip, hw, ho]
    exact ⟨hc, ⟨hsa, hz, hi, hb, hr, hat⟩, hstored⟩) hflags
  exact hs.consequence (by
    rintro inp work out ⟨hc, ⟨hsa, hz, hi, hb, hr⟩, hmask, hflags⟩
    exact ⟨hc, ⟨hsa, hz, hi, hb, hr, hflags⟩, hmask⟩) (by
      rintro inp work out ⟨hc, ⟨hsa, hz, hi, hb, hr, hmask⟩, hflags⟩
      exact ⟨hc, ⟨hsa, hz, hi, hb, hr⟩, hmask, hflags⟩) (by omega)

end JointThermoComplexity.Complexity.MotifDirectionInit

#print axioms JointThermoComplexity.Complexity.MotifDirectionInit.hoareTime
