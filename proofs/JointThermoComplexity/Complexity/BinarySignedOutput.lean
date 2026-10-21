module
public import proofs.JointThermoComplexity.Complexity.BinarySignedNormalize
public import proofs.JointThermoComplexity.Complexity.SignedBufferOutput

set_option autoImplicit false
@[expose] public section

/-! A complete actual binary signed-subtraction transducer with exact canonical integerCode output. -/

namespace JointThermoComplexity.Complexity.BinarySignedOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryDifferenceCursor BinaryDifferenceRuntime SignedBinaryDifference

variable {w : ℕ}

def machine (left right flag : Fin w) : TM (w + 1) :=
  seqTM (BinarySignedNormalize.machine left right flag) (SignedBufferOutput.machine (Fin.last w) flag.castSucc)

def timeBound (xs ys : List Bool) : ℕ := 7 * max xs.length ys.length + xs.length + ys.length + 30

theorem old_ne_last (j : Fin w) : j.castSucc ≠ Fin.last w := by
  intro he
  have hv := congrArg Fin.val he
  simp only [Fin.val_castSucc, Fin.val_last] at hv
  have hj := j.isLt
  omega

theorem old_work_eq (work work' : Fin (w + 1) → Tape)
    (hw : ∀ j, j ≠ Fin.last w → work' j = work j) :
    (fun j : Fin w => work' j.castSucc) = (fun j => work j.castSucc) :=
  funext (fun j => hw j.castSucc (old_ne_last j))

structure Serialized (left right flag : Fin w) (xs ys : List Bool) (work : Fin (w + 1) → Tape) : Prop where
  operands : Finish left right flag true xs ys (fun j => work j.castSucc)
  magnitudeBuffer : (work (Fin.last w)).HasBinaryString (magnitude xs ys)
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
      (fun inp work out => Cursor before input (emitted ++ code xs ys) inp work out ∧ Serialized left right flag xs ys work ∧ R (fun j => work j.castSucc))
      (timeBound xs ys) := by
  let R' : (Fin (w + 1) → Tape) → Prop := fun work =>
    Finish left right flag true xs ys (fun j => work j.castSucc) ∧ R (fun j => work j.castSucc)
  have hR' : ∀ work work', (∀ j, j ≠ Fin.last w → work' j = work j) → R' work → R' work' := by
    intro work work' hw hp
    simpa only [R', old_work_eq work work' hw] using hp
  have hn := BinarySignedNormalize.hoareTime left right flag sep xs ys before input emitted R hR
  have ho := SignedBufferOutput.hoareTime (Fin.last w) flag.castSucc (old_ne_last flag) (negative xs ys)
    (magnitude xs ys) before input emitted R' hR'
  have hfull := seqTM_hoareTime (BinarySignedNormalize.machine left right flag)
    (SignedBufferOutput.machine (Fin.last w) flag.castSucc) hn (by
      rintro inp work out ⟨hc, hp, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hp.safe, hp.magnitudeBuffer, hp.zero, hp.signValue, hp.operands, hr⟩) ho
  exact hfull.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hs, hm, hz, hf, hp, hr⟩
    exact ⟨hc, ⟨hp, hm, hz, hf, hs⟩, hr⟩) (by
      have hm := magnitude_length_le xs ys
      unfold timeBound BinarySignedNormalize.timeBound
      omega)

theorem integer_hoareTime (left right flag : Fin w) (sep : Separate left right flag)
    (xs ys before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ flag → work' j = work j) → R work → R work') :
    (machine left right flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        Start left right flag xs ys (fun j => work j.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (fun j => work j.castSucc))
      (fun inp work out => Cursor before input (emitted ++ BitCodec.integerCode (BinaryDifference.value xs - BinaryDifference.value ys)) inp work out ∧
        Serialized left right flag xs ys work ∧ R (fun j => work j.castSucc)) (timeBound xs ys) := by
  simpa only [code_correct] using hoareTime left right flag sep xs ys before input emitted R hR

theorem naturals_hoareTime (left right flag : Fin w) (sep : Separate left right flag)
    (x y : ℕ) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ flag → work' j = work j) → R work → R work') :
    (machine left right flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        Start left right flag x.bits y.bits (fun j => work j.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (fun j => work j.castSucc))
      (fun inp work out => Cursor before input (emitted ++ BitCodec.integerCode ((x : ℤ) - y)) inp work out ∧
        Serialized left right flag x.bits y.bits work ∧ R (fun j => work j.castSucc)) (timeBound x.bits y.bits) := by
  simpa only [BinaryDifference.value_bits] using integer_hoareTime left right flag sep x.bits y.bits before input emitted R hR

end JointThermoComplexity.Complexity.BinarySignedOutput

#print axioms JointThermoComplexity.Complexity.BinarySignedOutput.hoareTime
#print axioms JointThermoComplexity.Complexity.BinarySignedOutput.naturals_hoareTime
