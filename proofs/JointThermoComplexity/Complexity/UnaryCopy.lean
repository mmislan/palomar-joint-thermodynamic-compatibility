module
public import proofs.JointThermoComplexity.Complexity.UnaryReset
public import proofs.JointThermoComplexity.Complexity.CountSumAt

set_option autoImplicit false
@[expose] public section

/-! Overwrite an address with another bounded address, using a preserved zero scratch register. -/

namespace JointThermoComplexity.Complexity.UnaryCopy
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

theorem source_ne_destination (e : Fin (w + 1) ≃ Fin (w + 1)) (a : Fin w) :
    e a.castSucc ≠ CountSumAt.destination e := by
  intro h
  have he := e.injective h
  have hv := congrArg Fin.val he
  change a.val = w at hv
  omega

def machine (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w) : TM (w + 1) :=
  seqTM (clearWorkTM (CountSumAt.destination e)) (CountSumAt.machine e source zero)

theorem hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (source zero : Fin w) (old value : ℕ)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (machine e source zero).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg old (work (CountSumAt.destination e)) ∧ IsReg value (work (e source.castSucc)) ∧
        IsReg 0 (work (e zero.castSucc)) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg value (work (CountSumAt.destination e)) ∧ IsReg value (work (e source.castSucc)) ∧
        IsReg 0 (work (e zero.castSucc)) ∧ R work) (2 * old + 5 * value + 15) := by
  let P : (Fin (w + 1) → Tape) → Prop := fun work =>
    IsReg value (work (e source.castSucc)) ∧ IsReg 0 (work (e zero.castSucc)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hs, hz, hr⟩
    exact ⟨by simpa only [hw _ (source_ne_destination e source)] using hs,
      by simpa only [hw _ (source_ne_destination e zero)] using hz, hR work work' hw hr⟩
  have hreset := UnaryReset.hoareTime (CountSumAt.destination e) old before input emitted P hP
  have hcopy := CountSumAt.hoareTime e source zero value 0 before input emitted R hR
  have hseq := seqTM_hoareTime (clearWorkTM (CountSumAt.destination e)) (CountSumAt.machine e source zero) hreset (by
    rintro inp work out ⟨hc, hs, hd, hsrc, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hsrc, hz, hd, hc, hs, hr⟩) hcopy
  exact hseq.consequence (fun _ _ _ h => h)
    (fun _ _ _ ⟨hsrc, hz, hd, hc, hs, hr⟩ => ⟨hc, hs,
      by simpa only [Nat.add_zero] using hd, hsrc, hz, hr⟩) (by omega)

end JointThermoComplexity.Complexity.UnaryCopy

#print axioms JointThermoComplexity.Complexity.UnaryCopy.hoareTime
