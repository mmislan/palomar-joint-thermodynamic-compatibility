module
public import proofs.JointThermoComplexity.Complexity.OffsetWeightControl

set_option autoImplicit false
@[expose] public section

/-! Compute one offset weight in canonical scratch, preserving the source
coefficient. Scaling and constant addition are fixed before input. -/

namespace JointThermoComplexity.Complexity.OffsetWeightBuffer
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork cast_ne_last)
open OffsetWeightControl
variable {w : ℕ}

def bound (k a B : ℕ) : ℕ := 3 * B + 2 * k + 11 + a * (2 * (B + k) + 2 * a + 5)

def branch (k a : ℕ) (idx : Fin w) : TM (w + 1) :=
  seqTM (BinaryScaleBuffer.machine k idx) (BinaryConstantAdd.machine a (Fin.last w))

def select (k a : ℕ) (idx flag : Fin w) : TM (w + 1) :=
  WorkSymbolBranch.machine Γ.one flag.castSucc (branch 0 a idx) (branch k a idx)

def machine (t : ℤ) (d : ℕ) (idx sign adjusted : Fin w) : TM (w + 1) :=
  seqTM (SignAdjust.machine (decide (t < 0)) sign.castSucc adjusted.castSucc)
    (select (multiplier t d) (constant d) idx adjusted)

theorem bound_static (k a b B : ℕ) (hk : k ≤ 2592) (ha : a ≤ 16) (hb : b ≤ B) :
    bound k a b + 6 ≤ 35 * B + 88737 := by
  have ht : 2 * (b + k) + 2 * a + 5 ≤ 2 * (B + 2592) + 2 * 16 + 5 := by omega
  have hm := Nat.mul_le_mul ha ht
  unfold bound
  omega

theorem template_bound (t : ℤ) (d v B : ℕ) (ht : t.natAbs ≤ 81) (hd : d ≤ 4)
    (hv : v.bits.length ≤ B) : bound (multiplier t d) (constant d) v.bits.length + 6 ≤ 35 * B + 88737 := by
  have hs := static_bounds t d ht hd
  exact bound_static _ _ _ B hs.2 hs.1 hv

theorem bound_zero_le (k a B : ℕ) : bound 0 a B ≤ bound k a B := by
  have h : 2 * (B + 0) + 2 * a + 5 ≤ 2 * (B + k) + 2 * a + 5 := by omega
  have hm := Nat.mul_le_mul_left a h
  unfold bound
  omega

theorem branch_hoareTime (k a : ℕ) (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (branch k a idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ (work (Fin.last w)).HasBinaryPrefix [] ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ Register (k * v + a) (work (Fin.last w)) ∧ R (oldWork work))
      (bound k a v.bits.length) := by
  have hs := BinaryScaleBuffer.natural_hoareTime k idx v before input emitted R
  have ha := BinaryConstantAdd.hoareTime a (Fin.last w) (k * v) before input emitted
    (ScaledFactorPipeline.Keep idx v R) (ScaledFactorPipeline.keep_stable idx v R)
  have hf := seqTM_hoareTime _ _ hs (by
    rintro inp work out ⟨hc, hs, hv, hb, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hb, hv, hx⟩) ha
  apply hf.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hc, hs, hb, hv, hx⟩
    exact ⟨hc, hs, hv, hb, hx⟩
  · have hbits := TemplateFactorScratchBounds.product_bits k v
    have hterm : 2 * (k * v).bits.length + 2 * a + 5 ≤ 2 * (v.bits.length + k) + 2 * a + 5 := by omega
    have hm := Nat.mul_le_mul_left a hterm
    unfold bound
    omega

theorem select_hoareTime (k a : ℕ) (idx flag : Fin w) (v : ℕ) (negative : Bool)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (select k a idx flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ (work (Fin.last w)).HasBinaryPrefix [] ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ (work flag.castSucc).read = Γ.ofBool negative ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ Register (if negative then a else k * v + a) (work (Fin.last w)) ∧
        (work flag.castSucc).read = Γ.ofBool negative ∧ R (oldWork work))
      (bound k a v.bits.length + 2) := by
  cases negative with
  | false =>
    have hp := branch_hoareTime k a idx v before input emitted
      (fun work => (work flag).read = Γ.ofBool false ∧ R work)
    have hb := WorkSymbolBranch.no_hoareTime Γ.one flag.castSucc (branch 0 a idx) (branch k a idx)
      before input emitted before input emitted
      (fun work => (∀ j, Parked (work j)) ∧ Register v (work idx.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧
        (work flag.castSucc).read = Γ.ofBool false ∧ R (oldWork work))
      (fun work => (∀ j, Parked (work j)) ∧ Register v (work idx.castSucc) ∧
        Register (k * v + a) (work (Fin.last w)) ∧ (work flag.castSucc).read = Γ.ofBool false ∧ R (oldWork work))
      (bound k a v.bits.length) hp
    apply hb.consequence
    · rintro inp work out ⟨hc, hs, hv, hb, hz, hn, hx⟩
      exact ⟨⟨hc, hs, hv, hb, hz, hn, hx⟩, by rw [hn]; decide⟩
    · intro inp work out hp
      simpa only [Bool.false_eq_true, ↓reduceIte] using hp
    · exact le_rfl
  | true =>
    have hp := (branch_hoareTime 0 a idx v before input emitted
      (fun work => (work flag).read = Γ.ofBool true ∧ R work)).mono_bound (bound_zero_le k a v.bits.length)
    have hb := WorkSymbolBranch.yes_hoareTime Γ.one flag.castSucc (branch 0 a idx) (branch k a idx)
      before input emitted before input emitted
      (fun work => (∀ j, Parked (work j)) ∧ Register v (work idx.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧
        (work flag.castSucc).read = Γ.ofBool true ∧ R (oldWork work))
      (fun work => (∀ j, Parked (work j)) ∧ Register v (work idx.castSucc) ∧
        Register (0 * v + a) (work (Fin.last w)) ∧ (work flag.castSucc).read = Γ.ofBool true ∧ R (oldWork work))
      (bound k a v.bits.length) hp
    apply hb.consequence
    · rintro inp work out ⟨hc, hs, hv, hb, hz, hn, hx⟩
      exact ⟨⟨hc, hs, hv, hb, hz, hn, hx⟩, hn⟩
    · intro inp work out hp
      simpa only [↓reduceIte, Nat.zero_mul, Nat.zero_add] using hp
    · omega

theorem hoareTime (t : ℤ) (d v : ℕ) (negative : Bool) (idx sign adjusted : Fin w)
    (hi : idx ≠ adjusted) (hs : sign ≠ adjusted) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ adjusted → next j = work j) → R work → R next) :
    (machine t d idx sign adjusted).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ (work sign.castSucc).read = Γ.ofBool negative ∧
        (work adjusted.castSucc).head = 1 ∧ (work (Fin.last w)).HasBinaryPrefix [] ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ Register (weight negative v t d) (work (Fin.last w)) ∧
        (work sign.castSucc).read = Γ.ofBool negative ∧ (work adjusted.castSucc).head = 1 ∧
        (work adjusted.castSucc).read = Γ.ofBool (OffsetWeightControl.adjusted negative t) ∧ R (oldWork work))
      (bound (multiplier t d) (constant d) v.bits.length + 6) := by
  have ha := SignAdjust.hoareTime (decide (t < 0)) negative sign.castSucc adjusted.castSucc
    (TemplateFactorPipeline.cast_ne sign adjusted hs).symm before input emitted
    (RawTemplateFactor.Keep idx sign v negative R) (RawTemplateFactor.keep_stable idx sign adjusted hi hs v negative R hR)
  have hw := select_hoareTime (multiplier t d) (constant d) idx adjusted v
    (OffsetWeightControl.adjusted negative t) before input emitted
    (fun work => (work adjusted).head = 1 ∧ (work sign).read = Γ.ofBool negative ∧ R work)
  have hf := seqTM_hoareTime _ _ ha (by
    rintro inp work out ⟨hc, hs, hh, hn, ho, hv, _hn', hb, hz, hx⟩
    obtain ⟨hi, hw, hout⟩ := hc.phase
    rw [hi, hw, hout]
    exact ⟨hc, hs, hv, hb, hz, hn, hh, ho, hx⟩) hw
  apply hf.consequence
  · rintro inp work out ⟨hc, hs, hv, hn, hh, hb, hz, hx⟩
    exact ⟨hc, hs, hh, hn, hv, hn, hb, hz, hx⟩
  · rintro inp work out ⟨hc, hs, hv, hb, hn, hh, ho, hx⟩
    exact ⟨hc, hs, hv, hb, ho, hh, hn, hx⟩
  · omega

end JointThermoComplexity.Complexity.OffsetWeightBuffer

#print axioms JointThermoComplexity.Complexity.OffsetWeightBuffer.machine
#print axioms JointThermoComplexity.Complexity.OffsetWeightBuffer.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.OffsetWeightBuffer.hoareTime
#print axioms JointThermoComplexity.Complexity.OffsetWeightBuffer.template_bound
