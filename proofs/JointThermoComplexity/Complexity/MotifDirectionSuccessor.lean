module
public import proofs.JointThermoComplexity.Complexity.MotifDirectionFrame
public import proofs.JointThermoComplexity.Complexity.BoxSourceFrame
public import proofs.JointThermoComplexity.Complexity.UnarySuccessor

set_option autoImplicit false
@[expose] public section

/-! Advance the actual current-variable address while retaining both bit cursors and the separate species mask. -/

namespace JointThermoComplexity.Complexity.MotifDirectionSuccessor
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts MotifDirectionState MotifDirectionFrame PowerPorts MonomialPorts

theorem hoareTime (m L idx : ℕ) (mask flags : List Bool) (i : ℕ) (before input emitted : List Bool)
    (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (UnarySuccessor.machine (species (m + 1))).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ State m L idx mask flags i R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ State m L (idx + 1) mask flags i R work) (2 * idx + 6) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work => BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
    BoxState.Buffers m L work ∧ R work ∧ At mask i (work (buffer m 1)) ∧ At flags i (work (buffer m 2))
  have hP : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hz, hb, hr, hm, hf⟩
    have hfixed := BoxSourceFrame.frame m L (fun _ => True) (fun _ _ _ _ => trivial) work work' hw ⟨hz, hb, trivial⟩
    have hu : Unchanged m work work' := fun j _ _ hs => hw j hs
    exact ⟨hfixed.1, hfixed.2.1, hR work work' hu hr,
      by rw [hw (buffer m 1) (species_ne_accumulator (m + 1)).symm]; exact hm,
      by rw [hw (buffer m 2) (species_ne_power (m + 1)).symm]; exact hf⟩
  have hs := UnarySuccessor.hoareTime (species (m + 1)) idx before input emitted P hP
  exact hs.consequence (by
    rintro inp work out ⟨hc, ⟨hsa, hz, hi, hb, hr⟩, hm, hf⟩
    exact ⟨hc, hsa, hi, hz, hb, hr, hm, hf⟩) (by
      rintro inp work out ⟨hc, hsa, hi, hz, hb, hr, hm, hf⟩
      exact ⟨hc, ⟨hsa, hz, hi, hb, hr⟩, hm, hf⟩) le_rfl

end JointThermoComplexity.Complexity.MotifDirectionSuccessor

#print axioms JointThermoComplexity.Complexity.MotifDirectionSuccessor.hoareTime
