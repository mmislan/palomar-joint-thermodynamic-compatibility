module
public import proofs.JointThermoComplexity.Complexity.MaskReady

set_option autoImplicit false
@[expose] public section

/-! Actual fixed-width source-tag scanning on every word. Truncated tags fail
after copying only the available bits; the fuel register is restored. -/

namespace JointThermoComplexity.Complexity.SourceTags
open _root_.Complexity _root_.Complexity.TM HeaderAt

def parse : List Bool → Option ((Bool × Bool × Bool) × List Bool)
  | a :: b :: c :: rest => some ((a, b, c), rest)
  | _ => none

def accepted (input : List Bool) : Bool := decide (3 ≤ input.length)

theorem parse_iff (input : List Bool) : accepted input = true ↔ ∃ tag rest, parse input = some (tag, rest) := by
  cases input with
  | nil => simp [accepted, parse]
  | cons a input =>
    cases input with
    | nil => simp [accepted, parse]
    | cons b input =>
      cases input with
      | nil => simp [accepted, parse]
      | cons c input => simp [accepted, parse]

variable {n : ℕ}

def machine (fuel : Fin (n + 1)) : TM (n + 1) := MaskReady.machine fuel

theorem hoareTime (fuel : Fin (n + 1)) (hf : fuel ≠ NaturalMachine.flagIndex n)
    (before input emitted : List Bool) (R : (Fin (n + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ fuel → j ≠ NaturalMachine.flagIndex n → work' j = work j) → R work → R work') :
    (machine fuel).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧ IsReg 3 (work fuel) ∧ R work)
      (fun inp work out => Cursor (before ++ input.take 3) (input.drop 3) (emitted ++ input.take 3) inp work out ∧
        (work (NaturalMachine.flagIndex n)).head = 1 ∧
        (work (NaturalMachine.flagIndex n)).read = Γ.ofBool (accepted input) ∧ IsReg 3 (work fuel) ∧ R work) 16 := by
  have h := MaskReady.hoareTime fuel hf 3 before input emitted R hR
  apply h.strengthen_post
  rintro inp work out ⟨hr, hc, hh, hs, hstate⟩
  exact ⟨hc, hh, hs, hr, hstate⟩

end JointThermoComplexity.Complexity.SourceTags

#print axioms JointThermoComplexity.Complexity.SourceTags.parse_iff
#print axioms JointThermoComplexity.Complexity.SourceTags.hoareTime
