module
public import proofs.JointThermoComplexity.Complexity.UnaryPredecessor
public import proofs.JointThermoComplexity.Complexity.UnaryCopy

set_option autoImplicit false
@[expose] public section

/-! Preserve a positive next address while storing its predecessor in a separate result register. -/

namespace JointThermoComplexity.Complexity.CopyPredecessor
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w) : TM (w + 1) :=
  seqTM (UnaryCopy.machine e source zero) (UnaryPredecessor.machine (CountSumAt.destination e))

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w) (old v : ℕ)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (machine e source zero).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg old (work (CountSumAt.destination e)) ∧ IsReg (v + 1) (work (e source.castSucc)) ∧
        IsReg 0 (work (e zero.castSucc)) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg v (work (CountSumAt.destination e)) ∧ IsReg (v + 1) (work (e source.castSucc)) ∧
        IsReg 0 (work (e zero.castSucc)) ∧ R work) (2 * old + 7 * v + 33) := by
  let P : (Fin (w + 1) → Tape) → Prop := fun work => IsReg (v + 1) (work (e source.castSucc)) ∧
    IsReg 0 (work (e zero.castSucc)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hs, hz, hr⟩
    exact ⟨by simpa only [hw _ (UnaryCopy.source_ne_destination e source)] using hs,
      by simpa only [hw _ (UnaryCopy.source_ne_destination e zero)] using hz, hR work work' hw hr⟩
  have hc := UnaryCopy.hoareTime e source zero old (v + 1) before input emitted R hR
  have hp := UnaryPredecessor.hoareTime (CountSumAt.destination e) v before input emitted P hP
  have hseq := seqTM_hoareTime (UnaryCopy.machine e source zero) (UnaryPredecessor.machine (CountSumAt.destination e)) hc (by
    rintro inp work out ⟨hcur, hs, hd, hsrc, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨hcur, hs, hd, hsrc, hz, hr⟩) hp
  exact hseq.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp) (by omega)

end JointThermoComplexity.Complexity.CopyPredecessor

#print axioms JointThermoComplexity.Complexity.CopyPredecessor.hoareTime
