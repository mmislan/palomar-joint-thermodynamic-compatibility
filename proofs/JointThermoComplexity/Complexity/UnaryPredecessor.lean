module
public import proofs.JointThermoComplexity.Complexity.UnarySeekEnd
public import proofs.JointThermoComplexity.Complexity.CountRewind

set_option autoImplicit false
@[expose] public section

/-! Decrement a positive bounded address and return its canonical cell-one register. -/

namespace JointThermoComplexity.Complexity.UnaryPredecessor
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (idx : Fin w) : TM w :=
  seqTM (UnarySeekEnd.machine idx) (seqTM (UnaryTrimMachine.machine idx) (rewindWorkTM idx))

theorem hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg (v + 1) (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg v (work idx) ∧ R work)
      (2 * v + 12) := by
  have hs := UnarySeekEnd.hoareTime idx (v + 1) before input emitted R hR
  have ht := UnaryTrim.hoareTime idx v before input emitted R hR
  have hr := CountRewind.hoareTime idx v before input emitted R hR
  have hrest := seqTM_hoareTime (UnaryTrimMachine.machine idx) (rewindWorkTM idx) ht (by
    rintro inp work out ⟨hc, hsafe, hp, hz, hR⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hsafe, hp, hz, hR⟩) hr
  have hfull := seqTM_hoareTime (UnarySeekEnd.machine idx)
    (seqTM (UnaryTrimMachine.machine idx) (rewindWorkTM idx)) hs (by
      rintro inp work out ⟨hc, hsafe, hp, hz, hR⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hsafe, hp, hz, hR⟩) hrest
  exact hfull.consequence (fun _ _ _ hp => hp) (fun _ _ _ ⟨hv, hc, hsafe, hR⟩ => ⟨hc, hsafe, hv, hR⟩) (by omega)

end JointThermoComplexity.Complexity.UnaryPredecessor

#print axioms JointThermoComplexity.Complexity.UnaryPredecessor.hoareTime
