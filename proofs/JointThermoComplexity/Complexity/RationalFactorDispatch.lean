module
public import proofs.JointThermoComplexity.Complexity.RationalFactorEmission

set_option autoImplicit false
@[expose] public section

/-! The term-factor machine reads a retained sign flag at runtime. The frame
keeps that flag separate from the magnitude register consumed by increment. -/

namespace JointThermoComplexity.Complexity.RationalFactorDispatch
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun RationalFactorWords
variable {w : ℕ}

def machine (right : Bool) (idx sign : Fin w) : TM w :=
  WorkSymbolBranch.machine Γ.one sign (RationalFactorEmission.machine right true idx)
    (RationalFactorEmission.machine right false idx)

def Frame (sign : Fin w) (negative : Bool) (R : (Fin w → Tape) → Prop) (work : Fin w → Tape) : Prop :=
  (work sign).read = Γ.ofBool negative ∧ R work

theorem stable_frame (idx sign : Fin w) (hsep : idx ≠ sign) (negative : Bool)
    (R : (Fin w → Tape) → Prop) (hR : BinaryIncrementFramed.Stable idx R) :
    BinaryIncrementFramed.Stable idx (Frame sign negative R) := by
  intro work next he hf
  exact ⟨by rw [he sign hsep.symm]; exact hf.1, hR work next he hf.2⟩

theorem hoareTime (right negative : Bool) (idx sign : Fin w) (hsep : idx ≠ sign) (v : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : BinaryIncrementFramed.Stable idx R) :
    (machine right idx sign).HoareTime
      (RationalFactorEmission.Logical idx v before input emitted (Frame sign negative R))
      (RationalFactorEmission.Logical idx (RationalFactorEmission.valueAfter right v) before input
        (emitted ++ word right (coefficient negative v)) (Frame sign negative R))
      (5 * v.bits.length + 34) := by
  have hframe := stable_frame idx sign hsep negative R hR
  have hb := RationalFactorEmission.hoareTime right negative idx v before input emitted (Frame sign negative R) hframe
  cases negative
  · have h := WorkSymbolBranch.no_hoareTime Γ.one sign
      (RationalFactorEmission.machine right true idx) (RationalFactorEmission.machine right false idx)
      before input emitted before input (emitted ++ word right (coefficient false v))
      (fun work => (∀ j, Parked (work j)) ∧ Register v (work idx) ∧ Frame sign false R work)
      (fun work => (∀ j, Parked (work j)) ∧ Register (RationalFactorEmission.valueAfter right v) (work idx) ∧ Frame sign false R work)
      (5 * v.bits.length + 32) hb
    apply h.consequence
    · rintro inp work out hh
      exact ⟨hh, by rw [hh.2.2.2.1]; decide⟩
    · exact fun _ _ _ hh => hh
    · omega
  · have h := WorkSymbolBranch.yes_hoareTime Γ.one sign
      (RationalFactorEmission.machine right true idx) (RationalFactorEmission.machine right false idx)
      before input emitted before input (emitted ++ word right (coefficient true v))
      (fun work => (∀ j, Parked (work j)) ∧ Register v (work idx) ∧ Frame sign true R work)
      (fun work => (∀ j, Parked (work j)) ∧ Register (RationalFactorEmission.valueAfter right v) (work idx) ∧ Frame sign true R work)
      (5 * v.bits.length + 32) hb
    apply h.consequence
    · rintro inp work out hh
      exact ⟨hh, hh.2.2.2.1⟩
    · exact fun _ _ _ hh => hh
    · omega

theorem coefficient_sign_magnitude (c : ℤ) : coefficient (decide (c < 0)) c.natAbs = c := by
  cases c with
  | ofNat v => simp [coefficient]
  | negSucc v => simp [coefficient]; omega

theorem signed_hoareTime (right : Bool) (idx sign : Fin w) (hsep : idx ≠ sign) (c : ℤ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : BinaryIncrementFramed.Stable idx R) :
    (machine right idx sign).HoareTime
      (RationalFactorEmission.Logical idx c.natAbs before input emitted (Frame sign (decide (c < 0)) R))
      (RationalFactorEmission.Logical idx (RationalFactorEmission.valueAfter right c.natAbs) before input
        (emitted ++ word right c) (Frame sign (decide (c < 0)) R))
      (5 * c.natAbs.bits.length + 34) := by
  simpa only [coefficient_sign_magnitude] using hoareTime right (decide (c < 0)) idx sign hsep c.natAbs before input emitted R hR

end JointThermoComplexity.Complexity.RationalFactorDispatch

#print axioms JointThermoComplexity.Complexity.RationalFactorDispatch.machine
#print axioms JointThermoComplexity.Complexity.RationalFactorDispatch.hoareTime
#print axioms JointThermoComplexity.Complexity.RationalFactorDispatch.signed_hoareTime
