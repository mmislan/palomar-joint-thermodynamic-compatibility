module
public import proofs.JointThermoComplexity.Complexity.TemplateFactorScratchBounds

set_option autoImplicit false
@[expose] public section

/-! Exact template-factor emission followed by a proved scratch reset. This
interface can be repeated in one static template program without assuming a
fresh scratch tape on each iteration. -/

namespace JointThermoComplexity.Complexity.ReusableTemplateFactor
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork cast_ne_last)
variable {w : ℕ}

def machine (t : ℤ) (right : Bool) (idx sign adjusted : Fin w) : TM (w + 1) :=
  seqTM (TemplateFactorPipeline.machine t right idx sign adjusted) (BinaryBufferReset.machine (Fin.last w))

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
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (11 * c.natAbs.bits.length + 10 * t.natAbs + 62) := by
  let v := RationalFactorEmission.valueAfter right (t.natAbs * c.natAbs)
  let S : (Fin (w + 1) → Tape) → Prop := fun work =>
    Register c.natAbs (work idx.castSucc) ∧ (work sign.castSucc).read = Γ.ofBool (decide (c < 0)) ∧
    (work adjusted.castSucc).head = 1 ∧
    (work adjusted.castSucc).read = Γ.ofBool (Bool.xor (decide (c < 0)) (decide (t < 0))) ∧ R (oldWork work)
  have hS : ∀ work next, (∀ j, j ≠ Fin.last w → next j = work j) → S work → S next := by
    rintro work next he ⟨hv, hsign, hhead, hadjusted, hr⟩
    have hold : oldWork next = oldWork work := funext (fun j => he j.castSucc (cast_ne_last j))
    exact ⟨by rw [he idx.castSucc (cast_ne_last idx)]; exact hv,
      by rw [he sign.castSucc (cast_ne_last sign)]; exact hsign,
      by rw [he adjusted.castSucc (cast_ne_last adjusted)]; exact hhead,
      by rw [he adjusted.castSucc (cast_ne_last adjusted)]; exact hadjusted,
      by rw [hold]; exact hr⟩
  have hp := TemplateFactorPipeline.hoareTime t c right idx sign adjusted hi hs before input emitted R hR
  have hr := BinaryBufferReset.hoareTime (Fin.last w) v.bits before input
    (emitted ++ RationalFactorWords.word right (c * t)) S hS
  have hf := seqTM_hoareTime _ _ hp (by
    rintro inp work out ⟨hc, hsafe, hsrc, hsign, hhead, hadjusted, hscratch, hx⟩
    obtain ⟨hin, hw, hout⟩ := hc.phase
    rw [hin, hw, hout]
    exact ⟨hc, hsafe, hscratch.1.2, hscratch.2, by rw [hscratch.1.1]; omega,
      hsrc, hsign, hhead, hadjusted, hx⟩) hr
  apply hf.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hc, hsafe, hz, hsrc, hsign, hhead, hadjusted, hx⟩
    exact ⟨hc, hsafe, hsrc, hsign, hhead, hadjusted, CountTape.empty_prefix_of_zero hz, hz.cell0, hx⟩
  · have hb := TemplateFactorScratchBounds.valueAfter_bits right t.natAbs c.natAbs
    change 8 * c.natAbs.bits.length + 7 * t.natAbs + 49 + 1 + (3 * v.bits.length + 9) ≤
      11 * c.natAbs.bits.length + 10 * t.natAbs + 62
    dsimp only [v]
    omega

theorem bounded_hoareTime (t c : ℤ) (right : Bool) (idx sign adjusted : Fin w)
    (hi : idx ≠ adjusted) (hs : sign ≠ adjusted) (B K : ℕ)
    (hB : c.natAbs.bits.length ≤ B) (hK : t.natAbs ≤ K) (before input emitted : List Bool)
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
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (11 * B + 10 * K + 62) :=
  (hoareTime t c right idx sign adjusted hi hs before input emitted R hR).mono_bound (by omega)

end JointThermoComplexity.Complexity.ReusableTemplateFactor

#print axioms JointThermoComplexity.Complexity.ReusableTemplateFactor.machine
#print axioms JointThermoComplexity.Complexity.ReusableTemplateFactor.hoareTime
#print axioms JointThermoComplexity.Complexity.ReusableTemplateFactor.bounded_hoareTime
