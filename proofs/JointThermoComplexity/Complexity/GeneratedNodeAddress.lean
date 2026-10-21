module
public import proofs.JointThermoComplexity.Complexity.SelectedAddressArithmetic
public import proofs.JointThermoComplexity.Complexity.SaturatingAddressCut

set_option autoImplicit false
@[expose] public section

/-! Compute the exact node address from preserved main coordinates and input arity. -/

namespace JointThermoComplexity.Complexity.GeneratedNodeAddress
open _root_.Complexity _root_.Complexity.TM HeaderAt

def coordinates : Fin 32 := ⟨5, by decide⟩
def arity : Fin 32 := ⟨18, by decide⟩
def root : Fin 32 := ⟨19, by decide⟩
def zero : Fin 32 := ⟨27, by decide⟩
def adjusted : Fin 32 := ⟨28, by decide⟩

def corrected (termMode : Bool) (count : ℕ) : ℕ := if termMode then count - 3 else count

def correction (termMode : Bool) : TM 32 :=
  if termMode then SaturatingAddressCut.machine 3 adjusted else emitBitsTM []

def machine (termMode : Bool) : TM 32 :=
  seqTM (SelectedAddressArithmetic.machine adjusted coordinates zero (by decide) (by decide))
    (seqTM (correction termMode) (SelectedAddressArithmetic.machine root arity adjusted (by decide) (by decide)))

def Stable (R : (Fin 32 → Tape) → Prop) : Prop :=
  ∀ work work', (∀ j, j ≠ adjusted → j ≠ root → work' j = work j) → R work → R work'

theorem correction_hoareTime (mode : Bool) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ adjusted → work' j = work j) → R work → R work') :
    (correction mode).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ IsReg v (work adjusted) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg (corrected mode v) (work adjusted) ∧ R work) (6 * v + 45) := by
  cases mode with
  | false =>
    have h := FixedOutput.hoareTime [] before input emitted (fun work => IsReg v (work adjusted) ∧ R work)
    exact h.consequence (fun _ _ _ h => h)
      (fun _ _ _ hp => by simpa only [corrected, Bool.false_eq_true, ↓reduceIte, List.append_nil] using hp) (by simp)
  | true =>
    have h := SaturatingAddressCut.hoareTime 3 adjusted v v le_rfl before input emitted R hR
    exact h.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega)

theorem hoareTime (mode : Bool) (oldAdjusted oldRoot coords countArity : ℕ)
    (before input emitted : List Bool) (R : (Fin 32 → Tape) → Prop) (hR : Stable R) :
    (machine mode).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg oldAdjusted (work adjusted) ∧ IsReg oldRoot (work root) ∧ IsReg coords (work coordinates) ∧
        IsReg countArity (work arity) ∧ IsReg 0 (work zero) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg (corrected mode coords) (work adjusted) ∧ IsReg (countArity + corrected mode coords) (work root) ∧
        IsReg coords (work coordinates) ∧ IsReg countArity (work arity) ∧ IsReg 0 (work zero) ∧ R work)
      (2 * oldAdjusted + 2 * oldRoot + 16 * coords + 5 * countArity + 77) := by
  let C : (Fin 32 → Tape) → Prop := fun work => IsReg oldRoot (work root) ∧
    IsReg countArity (work arity) ∧ R work
  have hC : ∀ work work', (∀ j, j ≠ adjusted → work' j = work j) → C work → C work' := by
    rintro work work' he ⟨hr, ha, hf⟩
    exact ⟨by simpa only [he _ (by decide : root ≠ adjusted)] using hr,
      by simpa only [he _ (by decide : arity ≠ adjusted)] using ha,
      hR work work' (fun j hj _ => he j hj) hf⟩
  have hcopy := SelectedAddressArithmetic.copy_hoareTime adjusted coordinates zero (by decide) (by decide)
    oldAdjusted coords before input emitted C hC
  let D : (Fin 32 → Tape) → Prop := fun work => IsReg coords (work coordinates) ∧ IsReg 0 (work zero) ∧ C work
  have hD : ∀ work work', (∀ j, j ≠ adjusted → work' j = work j) → D work → D work' := by
    rintro work work' he ⟨hc, hz, hf⟩
    exact ⟨by simpa only [he _ (by decide : coordinates ≠ adjusted)] using hc,
      by simpa only [he _ (by decide : zero ≠ adjusted)] using hz, hC work work' he hf⟩
  have hcut := correction_hoareTime mode coords before input emitted D hD
  let E : (Fin 32 → Tape) → Prop := fun work => IsReg coords (work coordinates) ∧ IsReg 0 (work zero) ∧ R work
  have hE : ∀ work work', (∀ j, j ≠ root → work' j = work j) → E work → E work' := by
    rintro work work' he ⟨hc, hz, hf⟩
    exact ⟨by simpa only [he _ (by decide : coordinates ≠ root)] using hc,
      by simpa only [he _ (by decide : zero ≠ root)] using hz,
      hR work work' (fun j _ hj => he j hj) hf⟩
  have hsum := SelectedAddressArithmetic.hoareTime root arity adjusted (by decide) (by decide)
    oldRoot countArity (corrected mode coords) before input emitted E hE
  have hrest := seqTM_hoareTime (correction mode)
    (SelectedAddressArithmetic.machine root arity adjusted (by decide) (by decide)) hcut (by
      rintro inp work out ⟨hc, hs, ht, hcoords, hz, hr, ha, hf⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, hr, ha, ht, hcoords, hz, hf⟩) hsum
  have hfull := seqTM_hoareTime (SelectedAddressArithmetic.machine adjusted coordinates zero (by decide) (by decide))
    (seqTM (correction mode) (SelectedAddressArithmetic.machine root arity adjusted (by decide) (by decide))) hcopy (by
      rintro inp work out ⟨hc, hs, ht, hcoords, hz, hr, ha, hf⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, ht, hcoords, hz, hr, ha, hf⟩) hrest
  apply hfull.consequence
  · rintro inp work out ⟨hc, hs, ht, hr, hcoords, ha, hz, hf⟩
    exact ⟨hc, hs, ht, hcoords, hz, hr, ha, hf⟩
  · rintro inp work out ⟨hc, hs, hr, ha, ht, hcoords, hz, hf⟩
    exact ⟨hc, hs, ht, hr, hcoords, ha, hz, hf⟩
  · have hb : corrected mode coords ≤ coords := by cases mode <;> simp [corrected]
    omega

end JointThermoComplexity.Complexity.GeneratedNodeAddress

#print axioms JointThermoComplexity.Complexity.GeneratedNodeAddress.correction_hoareTime
#print axioms JointThermoComplexity.Complexity.GeneratedNodeAddress.hoareTime
