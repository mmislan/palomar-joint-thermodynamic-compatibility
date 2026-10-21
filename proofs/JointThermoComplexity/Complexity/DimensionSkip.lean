module
public import proofs.JointThermoComplexity.Complexity.HeaderSkip

set_option autoImplicit false
@[expose] public section

/-! Traverse all three unary dimensions without changing retained registers or output. -/

namespace JointThermoComplexity.Complexity.DimensionSkip
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt RealSyntax

variable {w : ℕ}

def code (n r c : ℕ) : List Bool := binderCode n ++ binderCode r ++ binderCode c

def machine : TM w := seqTM (seqTM HeaderSkip.machine HeaderSkip.machine) HeaderSkip.machine

theorem hoareTime (n r c : ℕ) (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before (code n r c ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (fun inp work out => Cursor (before ++ code n r c) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R work)
      (n + r + c + 5) := by
  have hn := HeaderSkip.hoareTime n before (binderCode r ++ binderCode c ++ tail) emitted R
  have hr := HeaderSkip.hoareTime r (before ++ binderCode n) (binderCode c ++ tail) emitted R
  have hc := HeaderSkip.hoareTime c ((before ++ binderCode n) ++ binderCode r) tail emitted R
  have hnr := seqTM_hoareTime HeaderSkip.machine HeaderSkip.machine hn (by
    rintro inp work out ⟨hcur, hs, hR⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [List.append_assoc] using hcur, hs, hR⟩) hr
  have hfull := seqTM_hoareTime (seqTM HeaderSkip.machine HeaderSkip.machine) HeaderSkip.machine hnr (by
    rintro inp work out ⟨hcur, hs, hR⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨hcur, hs, hR⟩) hc
  exact hfull.consequence
    (fun _ _ _ h => by simpa only [code, List.append_assoc] using h)
    (fun _ _ _ h => by simpa only [code, List.append_assoc] using h) (by omega)

end JointThermoComplexity.Complexity.DimensionSkip

#print axioms JointThermoComplexity.Complexity.DimensionSkip.hoareTime
