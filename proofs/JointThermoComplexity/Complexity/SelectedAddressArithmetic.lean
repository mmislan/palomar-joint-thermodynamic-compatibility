module
public import proofs.JointThermoComplexity.Complexity.UnaryCopy

set_option autoImplicit false
@[expose] public section

/-! Overwrite any selected address register by the sum of two preserved bounded registers. -/

namespace JointThermoComplexity.Complexity.SelectedAddressArithmetic
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def route (dst : Fin (w + 1)) : Fin (w + 1) ≃ Fin (w + 1) := Equiv.swap (Fin.last w) dst

theorem route_destination (dst : Fin (w + 1)) : CountSumAt.destination (route dst) = dst := by
  simp [CountSumAt.destination, route]

def operand (dst src : Fin (w + 1)) (h : src ≠ dst) : Fin w :=
  ⟨((route dst).symm src).val, by
    have hn : (route dst).symm src ≠ Fin.last w := by
      intro he
      apply h
      have hv := congrArg (route dst) he
      simpa [route] using hv
    have hi := ((route dst).symm src).isLt
    have hv : ((route dst).symm src).val ≠ w := fun he => hn (Fin.ext he)
    omega⟩

theorem operand_route (dst src : Fin (w + 1)) (h : src ≠ dst) :
    route dst (operand dst src h).castSucc = src := by
  have he : (operand dst src h).castSucc = (route dst).symm src := rfl
  rw [he, Equiv.apply_symm_apply]

def machine (dst a b : Fin (w + 1)) (ha : a ≠ dst) (hb : b ≠ dst) : TM (w + 1) :=
  seqTM (clearWorkTM dst) (CountSumAt.machine (route dst) (operand dst a ha) (operand dst b hb))

theorem hoareTime (dst a b : Fin (w + 1)) (ha : a ≠ dst) (hb : b ≠ dst) (old va vb : ℕ)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ dst → work' j = work j) → R work → R work') :
    (machine dst a b ha hb).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg old (work dst) ∧ IsReg va (work a) ∧ IsReg vb (work b) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg (va + vb) (work dst) ∧ IsReg va (work a) ∧ IsReg vb (work b) ∧ R work)
      (2 * old + 5 * (va + vb) + 15) := by
  let P : (Fin (w + 1) → Tape) → Prop := fun work => IsReg va (work a) ∧ IsReg vb (work b) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ dst → work' j = work j) → P work → P work' := by
    rintro work work' he ⟨hva, hvb, hr⟩
    exact ⟨by simpa only [he a ha] using hva, by simpa only [he b hb] using hvb, hR work work' he hr⟩
  have hc := UnaryReset.hoareTime dst old before input emitted P hP
  have hs := CountSumAt.hoareTime (route dst) (operand dst a ha) (operand dst b hb) va vb before input emitted R
    (by simpa only [route_destination] using hR)
  simp only [route_destination, operand_route] at hs
  have hseq := seqTM_hoareTime (clearWorkTM dst)
    (CountSumAt.machine (route dst) (operand dst a ha) (operand dst b hb)) hc (by
      rintro inp work out ⟨hcur, hw, hz, hva, hvb, hr⟩
      obtain ⟨hi, hworks, ho⟩ := hcur.phase
      rw [hi, hworks, ho]
      exact ⟨hva, hvb, hz, hcur, hw, hr⟩) hs
  exact hseq.consequence (fun _ _ _ h => h)
    (fun _ _ _ ⟨hva, hvb, hd, hc, hw, hr⟩ => ⟨hc, hw, hd, hva, hvb, hr⟩) (by omega)

theorem copy_hoareTime (dst src zero : Fin (w + 1)) (hs : src ≠ dst) (hz : zero ≠ dst) (old value : ℕ)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ dst → work' j = work j) → R work → R work') :
    (machine dst src zero hs hz).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg old (work dst) ∧ IsReg value (work src) ∧ IsReg 0 (work zero) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg value (work dst) ∧ IsReg value (work src) ∧ IsReg 0 (work zero) ∧ R work)
      (2 * old + 5 * value + 15) := by
  simpa only [Nat.add_zero] using hoareTime dst src zero hs hz old value 0 before input emitted R hR

end JointThermoComplexity.Complexity.SelectedAddressArithmetic

#print axioms JointThermoComplexity.Complexity.SelectedAddressArithmetic.hoareTime
#print axioms JointThermoComplexity.Complexity.SelectedAddressArithmetic.copy_hoareTime
