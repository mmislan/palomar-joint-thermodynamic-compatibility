module
public import proofs.JointThermoComplexity.Complexity.BinaryScaleBuffer
public import proofs.JointThermoComplexity.Complexity.RationalFactorDispatch

set_option autoImplicit false
@[expose] public section

/-! Actual fixed-constant coefficient scaling followed by signed rational
factor emission. The original coefficient/sign buffers and surrounding frame
survive; the final scratch magnitude is consumed only by the left factor. -/

namespace JointThermoComplexity.Complexity.ScaledFactorPipeline
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun RationalFactorWords
open BinaryScaleBuffer (oldWork cast_ne_last)
variable {w : ℕ}

def machine (k : ℕ) (right : Bool) (idx sign : Fin w) : TM (w + 1) :=
  seqTM (BinaryScaleBuffer.machine k idx)
    (RationalFactorDispatch.machine right (Fin.last w) sign.castSucc)

def Keep (idx : Fin w) (v : ℕ) (R : (Fin w → Tape) → Prop) (work : Fin (w + 1) → Tape) : Prop :=
  Register v (work idx.castSucc) ∧ R (oldWork work)

theorem keep_stable (idx : Fin w) (v : ℕ) (R : (Fin w → Tape) → Prop) :
    BinaryIncrementFramed.Stable (Fin.last w) (Keep idx v R) := by
  intro work next he hp
  have hold : oldWork next = oldWork work := by
    funext j
    exact he j.castSucc (cast_ne_last j)
  exact ⟨by rw [he idx.castSucc (cast_ne_last idx)]; exact hp.1, by rw [hold]; exact hp.2⟩

theorem hoareTime (k : ℕ) (right negative : Bool) (idx sign : Fin w) (v : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine k right idx sign).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ (work (Fin.last w)).HasBinaryPrefix [] ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ (work sign.castSucc).read = Γ.ofBool negative ∧ R (oldWork work))
      (fun inp work out => Cursor before input (emitted ++ word right (coefficient negative (k * v))) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register v (work idx.castSucc) ∧
        Register (RationalFactorEmission.valueAfter right (k * v)) (work (Fin.last w)) ∧
        (work sign.castSucc).read = Γ.ofBool negative ∧ R (oldWork work))
      (8 * v.bits.length + 7 * k + 45) := by
  have hb := BinaryScaleBuffer.natural_hoareTime k idx v before input emitted
    (fun work => (work sign).read = Γ.ofBool negative ∧ R work)
  have hf := RationalFactorDispatch.hoareTime right negative (Fin.last w) sign.castSucc
    (cast_ne_last sign).symm (k * v) before input emitted (Keep idx v R) (keep_stable idx v R)
  have h := seqTM_hoareTime _ _ hb (by
    rintro inp work out ⟨hc, hs, hsrc, hdst, hsign, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hdst, hsign, hsrc, hx⟩) hf
  apply h.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hc, hs, hd, hsign, hsrc, hx⟩
    exact ⟨hc, hs, hsrc, hd, hsign, hx⟩
  · have hl : (k * v).bits.length ≤ v.bits.length + k := by
      simpa only [BinaryScaleCanonical.multiply_bits] using BinaryScaleCanonical.length_multiply k v.bits
    omega

end JointThermoComplexity.Complexity.ScaledFactorPipeline

#print axioms JointThermoComplexity.Complexity.ScaledFactorPipeline.machine
#print axioms JointThermoComplexity.Complexity.ScaledFactorPipeline.hoareTime
