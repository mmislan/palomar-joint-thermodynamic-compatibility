module
public import proofs.JointThermoComplexity.Complexity.UnarySuccessorScan
public import proofs.JointThermoComplexity.Complexity.CountRewind

set_option autoImplicit false
@[expose] public section

/-! Increment a bounded runtime address and return its head to cell one. -/

namespace JointThermoComplexity.Complexity.UnarySuccessor
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (idx : Fin w) : TM w := seqTM (UnarySuccessorMachine.machine idx) (rewindWorkTM idx)

theorem hoareTime (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg v (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg (v + 1) (work idx) ∧ R work)
      (2 * v + 6) := by
  have hscan := UnarySuccessorScan.hoareTime idx v before input emitted R hR
  have hrew := CountRewind.hoareTime idx (v + 1) before input emitted R hR
  have hseq := seqTM_hoareTime (UnarySuccessorMachine.machine idx) (rewindWorkTM idx) hscan (by
    rintro inp work out ⟨hc, hs, hp, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hp, hz, hr⟩) hrew
  exact hseq.consequence (fun _ _ _ h => h)
    (fun _ _ _ ⟨hv, hc, hs, hr⟩ => ⟨hc, hs, hv, hr⟩) (by omega)

end JointThermoComplexity.Complexity.UnarySuccessor

#print axioms JointThermoComplexity.Complexity.UnarySuccessor.hoareTime
