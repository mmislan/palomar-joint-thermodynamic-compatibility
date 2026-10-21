module
public import proofs.JointThermoComplexity.Complexity.OffsetWeightBuffer
public import proofs.JointThermoComplexity.Complexity.BinaryAccumulator

set_option autoImplicit false
@[expose] public section

/-! Add one static template-row weight to the offset. Auxiliary and scratch
buffers are empty again afterwards, allowing repeated use of fixed tapes. -/

namespace JointThermoComplexity.Complexity.OffsetContribution
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork cast_ne_last)
variable {w : ℕ}

structure Separate (idx sign adjusted acc aux : Fin w) : Prop where
  idx_adjusted : idx ≠ adjusted
  sign_adjusted : sign ≠ adjusted
  acc_adjusted : acc ≠ adjusted
  aux_adjusted : aux ≠ adjusted
  idx_acc : idx ≠ acc
  sign_acc : sign ≠ acc
  idx_aux : idx ≠ aux
  sign_aux : sign ≠ aux
  acc_aux : acc ≠ aux

def Empty (t : Tape) : Prop := t.HasBinaryPrefix [] ∧ t.cells 0 = Γ.start

def Stable (adjusted acc aux : Fin w) (R : (Fin w → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ adjusted → j ≠ acc → j ≠ aux → next j = work j) → R work → R next

def Protected (idx sign adjusted : Fin w) (v : ℕ) (negative : Bool) (t : ℤ)
    (R : (Fin w → Tape) → Prop) (work : Fin w → Tape) : Prop :=
  Register v (work idx) ∧ (work sign).read = Γ.ofBool negative ∧ (work adjusted).head = 1 ∧
    (work adjusted).read = Γ.ofBool (OffsetWeightControl.adjusted negative t) ∧ R work

theorem protected_stable (idx sign adjusted target : Fin w) (hi : idx ≠ target) (hs : sign ≠ target)
    (ha : adjusted ≠ target) (v : ℕ) (negative : Bool) (t : ℤ) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ target → next j = work j) → R work → R next) :
    ∀ work next, (∀ j, j ≠ target → next j = work j) →
      Protected idx sign adjusted v negative t R work → Protected idx sign adjusted v negative t R next := by
  rintro work next he ⟨hv, hn, hh, hread, hx⟩
  exact ⟨by rw [he idx hi]; exact hv, by rw [he sign hs]; exact hn,
    by rw [he adjusted ha]; exact hh, by rw [he adjusted ha]; exact hread, hR work next he hx⟩

def machine (t : ℤ) (d : ℕ) (idx sign adjusted acc aux : Fin w) : TM (w + 1) :=
  seqTM (seqTM (seqTM (OffsetWeightBuffer.machine t d idx sign adjusted) (BinaryScratchRestore.machine aux))
    (BinaryAccumulator.machine acc aux)) (BinaryBufferReset.machine aux.castSucc)

theorem hoareTime (t : ℤ) (d v A : ℕ) (negative : Bool) (idx sign adjusted acc aux : Fin w)
    (sep : Separate idx sign adjusted acc aux) (ht : t.natAbs ≤ 81) (hd : d ≤ 4)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) (hR : Stable adjusted acc aux R) :
    (machine t d idx sign adjusted acc aux).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ (work sign.castSucc).read = Γ.ofBool negative ∧
        (work adjusted.castSucc).head = 1 ∧ Register A (work acc.castSucc) ∧
        Empty (work aux.castSucc) ∧ Empty (work (Fin.last w)) ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register v (work idx.castSucc) ∧ (work sign.castSucc).read = Γ.ofBool negative ∧
        (work adjusted.castSucc).head = 1 ∧
        (work adjusted.castSucc).read = Γ.ofBool (OffsetWeightControl.adjusted negative t) ∧
        Register (A + OffsetWeightControl.weight negative v t d) (work acc.castSucc) ∧
        Empty (work aux.castSucc) ∧ Empty (work (Fin.last w)) ∧ R (oldWork work))
      (13 * A.bits.length + 54 * v.bits.length + 138380) := by
  let q := OffsetWeightControl.weight negative v t d
  have hRa : ∀ work next, (∀ j, j ≠ adjusted → next j = work j) → R work → R next :=
    fun work next he => hR work next (fun j hj _ _ => he j hj)
  have hRu : ∀ work next, (∀ j, j ≠ aux → next j = work j) → R work → R next :=
    fun work next he => hR work next (fun j _ _ hj => he j hj)
  have hRc : ∀ work next, (∀ j, j ≠ acc → next j = work j) → R work → R next :=
    fun work next he => hR work next (fun j _ hj _ => he j hj)
  let W : (Fin w → Tape) → Prop := fun work => Register A (work acc) ∧ Empty (work aux) ∧ R work
  have hW : ∀ work next, (∀ j, j ≠ adjusted → next j = work j) → W work → W next := by
    rintro work next he ⟨hv, hz, hx⟩
    exact ⟨by rw [he acc sep.acc_adjusted]; exact hv,
      by rw [he aux sep.aux_adjusted]; exact hz, hRa work next he hx⟩
  let P := Protected idx sign adjusted v negative t R
  have hPu := protected_stable idx sign adjusted aux sep.idx_aux sep.sign_aux sep.aux_adjusted.symm v negative t R hRu
  have hPc := protected_stable idx sign adjusted acc sep.idx_acc sep.sign_acc sep.acc_adjusted.symm v negative t R hRc
  let U : (Fin w → Tape) → Prop := fun work => P work ∧ Register A (work acc)
  have hU : ∀ work next, (∀ j, j ≠ aux → next j = work j) → U work → U next := by
    rintro work next he ⟨hp, hv⟩
    exact ⟨hPu work next he hp, by rw [he acc sep.acc_aux]; exact hv⟩
  let Z : (Fin (w + 1) → Tape) → Prop := fun work =>
    Register (A + q) (work acc.castSucc) ∧ Empty (work (Fin.last w)) ∧ P (oldWork work)
  have hZ : ∀ work next, (∀ j, j ≠ aux.castSucc → next j = work j) → Z work → Z next := by
    rintro work next he ⟨hv, hz, hp⟩
    exact ⟨by rw [he acc.castSucc (TemplateFactorPipeline.cast_ne acc aux sep.acc_aux)]; exact hv,
      by rw [he (Fin.last w) (cast_ne_last aux).symm]; exact hz,
      hPu (oldWork work) (oldWork next) (fun j hj => he j.castSucc (TemplateFactorPipeline.cast_ne j aux hj)) hp⟩
  have hw := OffsetWeightBuffer.hoareTime t d v negative idx sign adjusted sep.idx_adjusted sep.sign_adjusted
    before input emitted W hW
  have hu := BinaryScratchRestore.hoareTime aux q before input emitted U hU
  have hc := BinaryAccumulator.hoareTime acc aux sep.acc_aux A q before input emitted P hPc
  have hz := BinaryBufferReset.hoareTime aux.castSucc q.bits before input emitted Z hZ
  have hwu := seqTM_hoareTime _ _ hw (by
    rintro inp work out ⟨hc, hs, hv, hq, hn, hh, hread, ha, hempty, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hempty.1, hempty.2, hq, ⟨hv, hn, hh, hread, hx⟩, ha⟩) hu
  have hwuc := seqTM_hoareTime _ _ hwu (by
    rintro inp work out ⟨hc, hs, hq, hb, hz, hp, ha⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, ha, hq, hb, hz, hp⟩) hc
  have hf := seqTM_hoareTime _ _ hwuc (by
    rintro inp work out ⟨hc, hs, ha, hq, hb, hz, hp⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hq.1.2, hq.2, by rw [hq.1.1]; omega, ha, ⟨hb, hz⟩, hp⟩) hz
  apply hf.consequence
  · rintro inp work out ⟨hc, hs, hv, hn, hh, ha, hu, hs0, hx⟩
    exact ⟨hc, hs, hv, hn, hh, hs0.1, hs0.2, ha, hu, hx⟩
  · rintro inp work out ⟨hc, hs, hu, ha, hs0, hv, hn, hh, hread, hx⟩
    exact ⟨hc, hs, hv, hn, hh, hread, ha,
      ⟨CountTape.empty_prefix_of_zero hu, hu.cell0⟩, hs0, hx⟩
  · have hw := OffsetWeightBuffer.template_bound t d v v.bits.length ht hd le_rfl
    have hstatic := OffsetWeightControl.static_bounds t d ht hd
    have hbits := OffsetWeightControl.bits_weight negative v t d
    have hq : q.bits.length ≤ v.bits.length + 2608 := by dsimp only [q]; omega
    omega

end JointThermoComplexity.Complexity.OffsetContribution

#print axioms JointThermoComplexity.Complexity.OffsetContribution.machine
#print axioms JointThermoComplexity.Complexity.OffsetContribution.hoareTime
