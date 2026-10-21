module
public import proofs.JointThermoComplexity.Complexity.BinaryCompareRewind
public import proofs.JointThermoComplexity.Complexity.BinaryMagnitudeSelect

set_option autoImplicit false
@[expose] public section

/-! Two real scans and bounded operand rewinds compute a sign and an unsigned padded magnitude. -/

namespace JointThermoComplexity.Complexity.BinarySignedRaw
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryDifferenceCursor BinaryDifferenceRuntime SignedBinaryDifference

variable {w : ℕ}

def machine (left right flag : Fin w) : TM w :=
  seqTM (BinaryCompareRewind.machine left right flag) (BinaryMagnitudeSelect.machine left right flag)

def timeBound (xs ys : List Bool) : ℕ := 2 * max xs.length ys.length + xs.length + ys.length + 13

theorem hoareTime (left right flag : Fin w) (sep : Separate left right flag)
    (xs ys before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ flag → work' j = work j) → R work → R work') :
    (machine left right flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Start left right flag xs ys work ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ BinaryMagnitudeSelect.rawMagnitude xs ys) inp work out ∧
        Finish left right flag true xs ys work ∧ (work flag).read = Γ.ofBool (negative xs ys) ∧ R work)
      (timeBound xs ys) := by
  have hc := BinaryCompareRewind.hoareTime left right flag sep xs ys before input emitted R hR
  have hm := BinaryMagnitudeSelect.hoareTime left right flag sep xs ys before input emitted R
    (fun work work' hw => hR work work' (fun j hl hr _ => hw j hl hr))
  have hs := seqTM_hoareTime (BinaryCompareRewind.machine left right flag) (BinaryMagnitudeSelect.machine left right flag) hc (by
    rintro inp work out ⟨hc, hp, hf, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp, by simpa only [negative] using hf, hr⟩) hm
  exact hs.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by
    unfold timeBound BinaryCompareRewind.timeBound
    omega)

theorem magnitude_value (xs ys : List Bool) :
    (if negative xs ys then -BinaryDifference.value (BinaryMagnitudeSelect.rawMagnitude xs ys)
      else BinaryDifference.value (BinaryMagnitudeSelect.rawMagnitude xs ys)) =
      BinaryDifference.value xs - BinaryDifference.value ys := by
  have hv := signed_value xs ys
  rw [← BinaryMagnitudeSelect.trim_raw, BinaryTrim.value_trim] at hv
  exact hv

end JointThermoComplexity.Complexity.BinarySignedRaw

#print axioms JointThermoComplexity.Complexity.BinarySignedRaw.hoareTime
#print axioms JointThermoComplexity.Complexity.BinarySignedRaw.magnitude_value
