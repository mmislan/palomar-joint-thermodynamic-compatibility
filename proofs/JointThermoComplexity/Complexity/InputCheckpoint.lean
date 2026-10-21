module
public import proofs.JointThermoComplexity.Complexity.InputPositionRun
public import proofs.JointThermoComplexity.Complexity.InputSeek
public import proofs.JointThermoComplexity.Complexity.InputRewind
public import proofs.JointThermoComplexity.Complexity.UnaryReset

set_option autoImplicit false
@[expose] public section

/-! Save a source cursor, restore it after lookahead, and clear the position scratch. -/

namespace JointThermoComplexity.Complexity.InputCheckpoint
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def save (idx : Fin w) : TM w := seqTM (InputPositionRun.machine idx) (InputSeek.machine idx)

def restore (idx : Fin w) : TM w := seqTM rewindInputTM (InputSeek.machine idx)

def restoreReset (idx : Fin w) : TM w := seqTM (restore idx) (clearWorkTM idx)

def around (idx : Fin w) (query : TM w) : TM w := seqTM (save idx) (seqTM query (restoreReset idx))

theorem save_hoareTime (idx : Fin w) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (save idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg before.length (work idx) ∧ R work) (6 * before.length + 9) := by
  have hs := InputPositionRun.hoareTime idx before input emitted R hR
  have hk := InputSeek.restore_exact_hoareTime idx before input emitted (fun work => (∀ j, Parked (work j)) ∧ R work)
  have hseq := seqTM_hoareTime (InputPositionRun.machine idx) (InputSeek.machine idx) hs (by
    rintro inp work out ⟨hc, hw, hp, hr⟩
    obtain ⟨hi, hworks, ho⟩ := hc.phase
    rw [hi, hworks, ho]
    exact ⟨hc, hp, hw, hr⟩) hk
  apply hseq.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hc, hp, hw, hr⟩
    exact ⟨hc, hw, hp, hr⟩
  · omega

theorem restore_hoareTime (idx : Fin w) (before input consumed remaining emitted : List Bool)
    (hsplit : consumed ++ remaining = before ++ input) (R : (Fin w → Tape) → Prop) :
    (restore idx).HoareTime
      (fun inp work out => Cursor consumed remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg before.length (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg before.length (work idx) ∧ R work) (consumed.length + 4 * before.length + 6) := by
  have hr := InputRewind.hoareTime consumed remaining emitted
    (fun work => (∀ j, Parked (work j)) ∧ IsReg before.length (work idx) ∧ R work)
  have hk := InputSeek.restore_exact_hoareTime idx before input emitted (fun work => (∀ j, Parked (work j)) ∧ R work)
  have hseq := seqTM_hoareTime (rewindInputTM (n := w)) (InputSeek.machine idx) hr (by
    rintro inp work out ⟨hc, hw, hp, hframe⟩
    rw [hsplit] at hc
    obtain ⟨hi, hworks, ho⟩ := hc.phase
    rw [hi, hworks, ho]
    exact ⟨hc, hp, hw, hframe⟩) hk
  apply hseq.consequence
  · rintro inp work out ⟨hc, hw, hp, hframe⟩
    exact ⟨hc, hw, hp, hframe⟩
  · rintro inp work out ⟨hc, hp, hw, hframe⟩
    exact ⟨hc, hw, hp, hframe⟩
  · omega

theorem restoreReset_hoareTime (idx : Fin w) (before input consumed remaining emitted : List Bool)
    (hsplit : consumed ++ remaining = before ++ input) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (restoreReset idx).HoareTime
      (fun inp work out => Cursor consumed remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg before.length (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work idx) ∧ R work) (consumed.length + 6 * before.length + 12) := by
  have hr := restore_hoareTime idx before input consumed remaining emitted hsplit R
  have hc := UnaryReset.hoareTime idx before.length before input emitted R hR
  have hseq := seqTM_hoareTime (restore idx) (clearWorkTM idx) hr (by
    rintro inp work out ⟨hcur, hw, hp, hframe⟩
    obtain ⟨hi, hworks, ho⟩ := hcur.phase
    rw [hi, hworks, ho]
    exact ⟨hcur, hw, hp, hframe⟩) hc
  exact hseq.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp) (by omega)

theorem around_hoareTime (idx : Fin w) (query : TM w)
    (before input consumed remaining emitted emitted' : List Bool)
    (hsplit : consumed ++ remaining = before ++ input) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') (B : ℕ)
    (hq : query.HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg before.length (work idx) ∧ R work)
      (fun inp work out => Cursor consumed remaining emitted' inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg before.length (work idx) ∧ R work) B) :
    (around idx query).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted' inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work idx) ∧ R work) (12 * before.length + consumed.length + B + 23) := by
  have hr := restoreReset_hoareTime idx before input consumed remaining emitted' hsplit R hR
  have hqr := seqTM_hoareTime query (restoreReset idx) hq (by
    rintro inp work out ⟨hc, hw, hp, hframe⟩
    obtain ⟨hi, hworks, ho⟩ := hc.phase
    rw [hi, hworks, ho]
    exact ⟨hc, hw, hp, hframe⟩) hr
  have hs := save_hoareTime idx before input emitted R hR
  have hseq := seqTM_hoareTime (save idx) (seqTM query (restoreReset idx)) hs (by
    rintro inp work out ⟨hc, hw, hp, hframe⟩
    obtain ⟨hi, hworks, ho⟩ := hc.phase
    rw [hi, hworks, ho]
    exact ⟨hc, hw, hp, hframe⟩) hqr
  exact hseq.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp) (by omega)

end JointThermoComplexity.Complexity.InputCheckpoint

#print axioms JointThermoComplexity.Complexity.InputCheckpoint.save_hoareTime
#print axioms JointThermoComplexity.Complexity.InputCheckpoint.restoreReset_hoareTime
#print axioms JointThermoComplexity.Complexity.InputCheckpoint.around_hoareTime
