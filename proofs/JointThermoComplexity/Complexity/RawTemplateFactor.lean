module
public import proofs.JointThermoComplexity.Complexity.ReusableTemplateFactor

set_option autoImplicit false
@[expose] public section

/-! The unchanged template-factor machine on arbitrary Boolean sign and
canonical natural magnitude, including raw negative zero. -/

namespace JointThermoComplexity.Complexity.RawTemplateFactor
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork cast_ne_last)
variable {w : ℕ}

def Keep (idx sign : Fin w) (v : ℕ) (negative : Bool) (R : (Fin w → Tape) → Prop)
    (work : Fin (w + 1) → Tape) : Prop :=
  Register v (work idx.castSucc) ∧ (work sign.castSucc).read = Γ.ofBool negative ∧
  (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work)

theorem keep_stable (idx sign adjusted : Fin w) (hi : idx ≠ adjusted) (hs : sign ≠ adjusted)
    (v : ℕ) (negative : Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ adjusted → next j = work j) → R work → R next) :
    ∀ work next, (∀ j, j ≠ adjusted.castSucc → next j = work j) →
      Keep idx sign v negative R work → Keep idx sign v negative R next := by
  rintro work next he ⟨hv, hn, hb, hz, hx⟩
  exact ⟨by rw [he idx.castSucc (TemplateFactorPipeline.cast_ne idx adjusted hi)]; exact hv,
    by rw [he sign.castSucc (TemplateFactorPipeline.cast_ne sign adjusted hs)]; exact hn,
    by rw [he (Fin.last w) (cast_ne_last adjusted).symm]; exact hb,
    by rw [he (Fin.last w) (cast_ne_last adjusted).symm]; exact hz,
    hR (oldWork work) (oldWork next) (fun j hj => he j.castSucc (TemplateFactorPipeline.cast_ne j adjusted hj)) hx⟩

theorem hoareTime (t : ℤ) (v : ℕ) (negative right : Bool) (idx sign adjusted : Fin w)
    (hi : idx ≠ adjusted) (hs : sign ≠ adjusted) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ adjusted → next j = work j) → R work → R next) :
    (ReusableTemplateFactor.machine t right idx sign adjusted).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ (work sign.castSucc).read = Γ.ofBool negative ∧
        (work adjusted.castSucc).head = 1 ∧ (work (Fin.last w)).HasBinaryPrefix [] ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor before input
          (emitted ++ RationalFactorWords.word right
            (RationalFactorWords.coefficient (Bool.xor negative (decide (t < 0))) (t.natAbs * v))) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register v (work idx.castSucc) ∧
        (work sign.castSucc).read = Γ.ofBool negative ∧ (work adjusted.castSucc).head = 1 ∧
        (work adjusted.castSucc).read = Γ.ofBool (Bool.xor negative (decide (t < 0))) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (11 * v.bits.length + 10 * t.natAbs + 62) := by
  have ha := SignAdjust.hoareTime (decide (t < 0)) negative sign.castSucc adjusted.castSucc
    (TemplateFactorPipeline.cast_ne sign adjusted hs).symm before input emitted
    (Keep idx sign v negative R) (keep_stable idx sign adjusted hi hs v negative R hR)
  have hp := ScaledFactorPipeline.hoareTime t.natAbs right (Bool.xor negative (decide (t < 0))) idx adjusted v
    before input emitted (fun work => (work adjusted).head = 1 ∧ (work sign).read = Γ.ofBool negative ∧ R work)
  have hap := seqTM_hoareTime _ _ ha (by
    rintro inp work out ⟨hc, hs, hh, hn, ho, hv, _hn', hb, hz, hx⟩
    obtain ⟨hi, hw, hout⟩ := hc.phase
    rw [hi, hw, hout]
    exact ⟨hc, hs, hv, hb, hz, hn, hh, ho, hx⟩) hp
  let S : (Fin (w + 1) → Tape) → Prop := fun work => Register v (work idx.castSucc) ∧
    (work sign.castSucc).read = Γ.ofBool negative ∧ (work adjusted.castSucc).head = 1 ∧
    (work adjusted.castSucc).read = Γ.ofBool (Bool.xor negative (decide (t < 0))) ∧ R (oldWork work)
  have hS : ∀ work next, (∀ j, j ≠ Fin.last w → next j = work j) → S work → S next := by
    rintro work next he ⟨hv, hn, hh, ha, hx⟩
    have hold : oldWork next = oldWork work := funext (fun j => he j.castSucc (cast_ne_last j))
    exact ⟨by rw [he idx.castSucc (cast_ne_last idx)]; exact hv,
      by rw [he sign.castSucc (cast_ne_last sign)]; exact hn,
      by rw [he adjusted.castSucc (cast_ne_last adjusted)]; exact hh,
      by rw [he adjusted.castSucc (cast_ne_last adjusted)]; exact ha,
      by rw [hold]; exact hx⟩
  have hr := BinaryBufferReset.hoareTime (Fin.last w)
    (RationalFactorEmission.valueAfter right (t.natAbs * v)).bits before input
    (emitted ++ RationalFactorWords.word right
      (RationalFactorWords.coefficient (Bool.xor negative (decide (t < 0))) (t.natAbs * v))) S hS
  have hf := seqTM_hoareTime _ _ hap (by
    rintro inp work out ⟨hc, hs, hv, hb, hn, hh, ho, hx⟩
    obtain ⟨hi, hw, hout⟩ := hc.phase
    rw [hi, hw, hout]
    exact ⟨hc, hs, hb.1.2, hb.2, by rw [hb.1.1]; omega, hv, ho, hh, hn, hx⟩) hr
  apply hf.consequence
  · rintro inp work out ⟨hc, hs, hv, hn, hh, hb, hz, hx⟩
    exact ⟨hc, hs, hh, hn, hv, hn, hb, hz, hx⟩
  · rintro inp work out ⟨hc, hs, hz, hv, hn, hh, ha, hx⟩
    exact ⟨hc, hs, hv, hn, hh, ha, CountTape.empty_prefix_of_zero hz, hz.cell0, hx⟩
  · have hb := TemplateFactorScratchBounds.valueAfter_bits right t.natAbs v
    omega

end JointThermoComplexity.Complexity.RawTemplateFactor

#print axioms JointThermoComplexity.Complexity.RawTemplateFactor.hoareTime
