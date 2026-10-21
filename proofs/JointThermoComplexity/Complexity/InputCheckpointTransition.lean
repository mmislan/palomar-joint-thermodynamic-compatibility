module
public import proofs.JointThermoComplexity.Complexity.InputCheckpoint

set_option autoImplicit false
@[expose] public section

/-! Lookahead may change its result registers while restoring the exact source cursor. -/

namespace JointThermoComplexity.Complexity.InputCheckpointTransition
open _root_.Complexity _root_.Complexity.TM HeaderAt InputCheckpoint
variable {w : ℕ}

theorem hoareTime (idx : Fin w) (query : TM w)
    (before input consumed remaining emitted emitted' : List Bool)
    (hsplit : consumed ++ remaining = before ++ input) (P Q : (Fin w → Tape) → Prop)
    (hP : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → P work → P work')
    (hQ : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → Q work → Q work') (B : ℕ)
    (hq : query.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg before.length (work idx) ∧ P work)
      (fun inp work out => Cursor consumed remaining emitted' inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg before.length (work idx) ∧ Q work) B) :
    (around idx query).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work idx) ∧ P work)
      (fun inp work out => Cursor before input emitted' inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work idx) ∧ Q work) (12 * before.length + consumed.length + B + 23) := by
  have hr := restoreReset_hoareTime idx before input consumed remaining emitted' hsplit Q hQ
  have hqr := seqTM_hoareTime query (restoreReset idx) hq (by
    rintro inp work out ⟨hc, hw, hp, hframe⟩
    obtain ⟨hi, hworks, ho⟩ := hc.phase
    rw [hi, hworks, ho]
    exact ⟨hc, hw, hp, hframe⟩) hr
  have hs := save_hoareTime idx before input emitted P hP
  have hseq := seqTM_hoareTime (save idx) (seqTM query (restoreReset idx)) hs (by
    rintro inp work out ⟨hc, hw, hp, hframe⟩
    obtain ⟨hi, hworks, ho⟩ := hc.phase
    rw [hi, hworks, ho]
    exact ⟨hc, hw, hp, hframe⟩) hqr
  exact hseq.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp) (by omega)

end JointThermoComplexity.Complexity.InputCheckpointTransition

#print axioms JointThermoComplexity.Complexity.InputCheckpointTransition.hoareTime
