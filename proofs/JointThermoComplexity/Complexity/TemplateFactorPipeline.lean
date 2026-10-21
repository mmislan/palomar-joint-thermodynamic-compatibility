module
public import proofs.JointThermoComplexity.Complexity.SignedProductControl
public import proofs.JointThermoComplexity.Complexity.SignAdjust
public import proofs.JointThermoComplexity.Complexity.ScaledFactorPipeline

set_option autoImplicit false
@[expose] public section

/-! One static template coefficient times a variable source coefficient,
followed by exact rational factor emission. Sign adjustment is an actual TM
step on a separate flag, leaving the original sign and magnitude available. -/

namespace JointThermoComplexity.Complexity.TemplateFactorPipeline
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork cast_ne_last)
variable {w : ℕ}

theorem cast_ne (i j : Fin w) (hij : i ≠ j) : i.castSucc ≠ j.castSucc := by
  intro h
  apply hij
  apply Fin.ext
  exact congrArg (fun x : Fin (w + 1) => x.val) h

def machine (t : ℤ) (right : Bool) (idx sign adjusted : Fin w) : TM (w + 1) :=
  seqTM (SignAdjust.machine (decide (t < 0)) sign.castSucc adjusted.castSucc)
    (ScaledFactorPipeline.machine t.natAbs right idx adjusted)

def Keep (idx sign : Fin w) (c : ℤ) (R : (Fin w → Tape) → Prop) (work : Fin (w + 1) → Tape) : Prop :=
  Register c.natAbs (work idx.castSucc) ∧ (work sign.castSucc).read = Γ.ofBool (decide (c < 0)) ∧
  (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work)

theorem keep_stable (idx sign adjusted : Fin w) (hi : idx ≠ adjusted) (hs : sign ≠ adjusted)
    (c : ℤ) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ adjusted → next j = work j) → R work → R next) :
    ∀ work next, (∀ j, j ≠ adjusted.castSucc → next j = work j) → Keep idx sign c R work → Keep idx sign c R next := by
  rintro work next he ⟨hv, hsign, hbits, hz, hx⟩
  exact ⟨by rw [he idx.castSucc (cast_ne idx adjusted hi)]; exact hv,
    by rw [he sign.castSucc (cast_ne sign adjusted hs)]; exact hsign,
    by rw [he (Fin.last w) (cast_ne_last adjusted).symm]; exact hbits,
    by rw [he (Fin.last w) (cast_ne_last adjusted).symm]; exact hz,
    hR (oldWork work) (oldWork next) (fun j hj => he j.castSucc (cast_ne j adjusted hj)) hx⟩

theorem hoareTime (t c : ℤ) (right : Bool) (idx sign adjusted : Fin w)
    (hi : idx ≠ adjusted) (hs : sign ≠ adjusted) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ adjusted → next j = work j) → R work → R next) :
    (machine t right idx sign adjusted).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register c.natAbs (work idx.castSucc) ∧ (work sign.castSucc).read = Γ.ofBool (decide (c < 0)) ∧
        (work adjusted.castSucc).head = 1 ∧ (work (Fin.last w)).HasBinaryPrefix [] ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor before input (emitted ++ RationalFactorWords.word right (c * t)) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register c.natAbs (work idx.castSucc) ∧
        (work sign.castSucc).read = Γ.ofBool (decide (c < 0)) ∧ (work adjusted.castSucc).head = 1 ∧
        (work adjusted.castSucc).read = Γ.ofBool (Bool.xor (decide (c < 0)) (decide (t < 0))) ∧
        Register (RationalFactorEmission.valueAfter right (t.natAbs * c.natAbs)) (work (Fin.last w)) ∧ R (oldWork work))
      (8 * c.natAbs.bits.length + 7 * t.natAbs + 49) := by
  have ha := SignAdjust.hoareTime (decide (t < 0)) (decide (c < 0)) sign.castSucc adjusted.castSucc
    (cast_ne sign adjusted hs).symm before input emitted (Keep idx sign c R) (keep_stable idx sign adjusted hi hs c R hR)
  have hf := ScaledFactorPipeline.hoareTime t.natAbs right (Bool.xor (decide (c < 0)) (decide (t < 0))) idx adjusted c.natAbs
    before input emitted (fun work => (work adjusted).head = 1 ∧ (work sign).read = Γ.ofBool (decide (c < 0)) ∧ R work)
  have h := seqTM_hoareTime _ _ ha (by
    rintro inp work out ⟨hc, hsafe, hhead, hadjusted, horiginal, hsrc, _hduplicate, hbits, hz, hx⟩
    obtain ⟨hin, hw, hout⟩ := hc.phase
    rw [hin, hw, hout]
    exact ⟨hc, hsafe, hsrc, hbits, hz, hadjusted, hhead, horiginal, hx⟩) hf
  rw [SignedProductControl.coefficient_product] at h
  apply h.consequence
  · rintro inp work out ⟨hc, hsafe, hv, hsign, hhead, hbits, hz, hx⟩
    exact ⟨hc, hsafe, hhead, hsign, hv, hsign, hbits, hz, hx⟩
  · rintro inp work out ⟨hc, hsafe, hv, hscratch, hadjusted, hhead, hsign, hx⟩
    exact ⟨hc, hsafe, hv, hsign, hhead, hadjusted, hscratch, hx⟩
  · omega

end JointThermoComplexity.Complexity.TemplateFactorPipeline

#print axioms JointThermoComplexity.Complexity.TemplateFactorPipeline.machine
#print axioms JointThermoComplexity.Complexity.TemplateFactorPipeline.hoareTime
