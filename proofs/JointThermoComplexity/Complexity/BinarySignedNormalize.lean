module
public import proofs.JointThermoComplexity.Complexity.BinarySignedBuffer
public import proofs.JointThermoComplexity.Complexity.BinaryTrimRuntime

set_option autoImplicit false
@[expose] public section

/-! Actual signed subtraction and high-zero erasure produce the exact canonical magnitude buffer. -/

namespace JointThermoComplexity.Complexity.BinarySignedNormalize
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryDifferenceCursor BinaryDifferenceRuntime SignedBinaryDifference

variable {w : ℕ}

def machine (left right flag : Fin w) : TM (w + 1) :=
  seqTM (BinarySignedBuffer.machine left right flag) (BinaryTrimMachine.machine (Fin.last w))

def timeBound (xs ys : List Bool) : ℕ := 3 * max xs.length ys.length + xs.length + ys.length + 16

structure Normalized (left right flag : Fin w) (xs ys : List Bool) (work : Fin (w + 1) → Tape) : Prop where
  operands : Finish left right flag true xs ys (fun j => work j.castSucc)
  magnitudeBuffer : (work (Fin.last w)).HasBinaryPrefix (magnitude xs ys)
  zero : (work (Fin.last w)).cells 0 = Γ.start
  signValue : (work flag.castSucc).read = Γ.ofBool (negative xs ys)
  safe : ∀ j, Parked (work j)

theorem hoareTime (left right flag : Fin w) (sep : Separate left right flag)
    (xs ys before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ flag → work' j = work j) → R work → R work') :
    (machine left right flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        Start left right flag xs ys (fun j => work j.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (fun j => work j.castSucc))
      (fun inp work out => Cursor before input emitted inp work out ∧ Normalized left right flag xs ys work ∧ R (fun j => work j.castSucc))
      (timeBound xs ys) := by
  let R' : (Fin (w + 1) → Tape) → Prop := fun work =>
    Finish left right flag true xs ys (fun j => work j.castSucc) ∧
    (work flag.castSucc).read = Γ.ofBool (negative xs ys) ∧ R (fun j => work j.castSucc)
  have hR' : ∀ work work', (∀ j, j ≠ Fin.last w → work' j = work j) → R' work → R' work' := by
    rintro work work' hw ⟨hp, hf, hr⟩
    have hne : ∀ j : Fin w, j.castSucc ≠ Fin.last w := by
      intro j he
      have hv := congrArg Fin.val he
      simp only [Fin.val_castSucc, Fin.val_last] at hv
      have hj := j.isLt
      omega
    have he : (fun j : Fin w => work' j.castSucc) = (fun j => work j.castSucc) :=
      funext (fun j => hw j.castSucc (hne j))
    exact ⟨by simpa only [he] using hp, by simpa only [hw flag.castSucc (hne flag)] using hf,
      by simpa only [he] using hr⟩
  have hb := BinarySignedBuffer.hoareTime left right flag sep xs ys before input emitted R hR
  have ht := BinaryTrimRuntime.hoareTime (Fin.last w) (BinaryMagnitudeSelect.rawMagnitude xs ys) before input emitted R' hR'
  have hs := seqTM_hoareTime (BinarySignedBuffer.machine left right flag) (BinaryTrimMachine.machine (Fin.last w)) hb (by
    rintro inp work out ⟨hc, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp.safe, hp.magnitude, hp.zero, hp.operands, hp.signValue, hr⟩) ht
  exact hs.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hs, hm, hz, hp, hf, hr⟩
    exact ⟨hc, ⟨hp, by simpa only [BinaryMagnitudeSelect.trim_raw] using hm, hz, hf, hs⟩, hr⟩) (by
      unfold timeBound BinarySignedRaw.timeBound
      rw [BinaryMagnitudeSelect.raw_length]
      omega)

end JointThermoComplexity.Complexity.BinarySignedNormalize

#print axioms JointThermoComplexity.Complexity.BinarySignedNormalize.hoareTime
