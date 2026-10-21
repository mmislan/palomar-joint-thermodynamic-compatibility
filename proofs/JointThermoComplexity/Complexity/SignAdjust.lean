module
public import proofs.JointThermoComplexity.Complexity.SourceTermToken
public import proofs.JointThermoComplexity.Complexity.WorkSymbolBranch

set_option autoImplicit false
@[expose] public section

/-! Compute a static sign xor into a separate work flag without consuming
input/output or the original sign flag. Existing branch/set primitives suffice. -/

namespace JointThermoComplexity.Complexity.SignAdjust
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def machine (flip : Bool) (source destination : Fin w) : TM w :=
  WorkSymbolBranch.machine Γ.one source (SourceTermToken.setStatus destination (!flip))
    (SourceTermToken.setStatus destination flip)

theorem hoareTime (flip negative : Bool) (source destination : Fin w) (hsep : destination ≠ source)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ destination → next j = work j) → R work → R next) :
    (machine flip source destination).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).head = 1 ∧ (work source).read = Γ.ofBool negative ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).head = 1 ∧ (work destination).read = Γ.ofBool (Bool.xor negative flip) ∧
        (work source).read = Γ.ofBool negative ∧ R work) 3 := by
  let S : (Fin w → Tape) → Prop := fun work => (work source).read = Γ.ofBool negative ∧ R work
  have hS : ∀ work next, (∀ j, j ≠ destination → next j = work j) → S work → S next := by
    rintro work next he ⟨hs, hr⟩
    exact ⟨by rw [he source hsep.symm]; exact hs, hR work next he hr⟩
  cases negative
  · have hb := SourceTermToken.setStatus_hoareTime destination flip before input emitted S hS
    have h := WorkSymbolBranch.no_hoareTime Γ.one source
      (SourceTermToken.setStatus destination (!flip)) (SourceTermToken.setStatus destination flip)
      before input emitted before input emitted
      (fun work => (∀ j, Parked (work j)) ∧ (work destination).head = 1 ∧ S work)
      (fun work => (∀ j, Parked (work j)) ∧ (work destination).head = 1 ∧
        (work destination).read = Γ.ofBool flip ∧ S work) 1 hb
    apply h.consequence
    · rintro inp work out hh
      exact ⟨hh, by rw [hh.2.2.2.1]; decide⟩
    · intro inp work out hh
      simpa [S, Bool.xor] using hh
    · omega
  · have hb := SourceTermToken.setStatus_hoareTime destination (!flip) before input emitted S hS
    have h := WorkSymbolBranch.yes_hoareTime Γ.one source
      (SourceTermToken.setStatus destination (!flip)) (SourceTermToken.setStatus destination flip)
      before input emitted before input emitted
      (fun work => (∀ j, Parked (work j)) ∧ (work destination).head = 1 ∧ S work)
      (fun work => (∀ j, Parked (work j)) ∧ (work destination).head = 1 ∧
        (work destination).read = Γ.ofBool (!flip) ∧ S work) 1 hb
    apply h.consequence
    · rintro inp work out hh
      exact ⟨hh, hh.2.2.2.1⟩
    · intro inp work out hh
      simpa [S, Bool.xor] using hh
    · omega

end JointThermoComplexity.Complexity.SignAdjust

#print axioms JointThermoComplexity.Complexity.SignAdjust.machine
#print axioms JointThermoComplexity.Complexity.SignAdjust.hoareTime
