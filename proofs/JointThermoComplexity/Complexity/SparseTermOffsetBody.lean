module
public import proofs.JointThermoComplexity.Complexity.SparseOffsetLayout
public import proofs.JointThermoComplexity.Complexity.SparseTermOffsetControl

set_option autoImplicit false
@[expose] public section

/-! A complete raw sparse-term step: parse coefficient/references, add its
concrete normalized offset weight, and retain reusable source buffers. -/

namespace JointThermoComplexity.Complexity.SparseTermOffsetBody
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork cast_ne_last)
open SparseOffsetLayout (Layout)
open OffsetContribution (Empty)
variable {w : ℕ}

def machine (boxed : Bool) (d : Layout w) : TM (w + 1) :=
  seqTM (SparseTermCanonicalLoad.machine d.Physical d.ending.castSucc d.flag.castSucc d.idx.castSucc d.sign.castSucc)
    (OffsetTemplateDispatch.machine boxed d.Physical d.ending.castSucc d.flag.castSucc d.idx d.sign d.adjusted d.acc d.aux)

def Fields (L : ℕ) (d : Layout w) (A : ℕ) (R : (Fin w → Tape) → Prop)
    (work : Fin (w + 1) → Tape) : Prop :=
  SparseOffsetLayout.Ready L d (oldWork work) ∧ (work d.adjusted.castSucc).head = 1 ∧
    Register A (work d.acc.castSucc) ∧ Empty (work d.aux.castSucc) ∧ Empty (work (Fin.last w)) ∧ R (oldWork work)

def Inv (L : ℕ) (d : Layout w) (A : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Fields L d A R work

def Post (L : ℕ) (boxed : Bool) (d : Layout w) (A : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) := fun inp work out =>
  Inv L d (A + SparseTermOffsetControl.delta boxed input)
      (before ++ SparseTermOffsetControl.taken input) (SparseTermOffsetControl.rest input) emitted R inp work out ∧
    Register (SignedRawControl.magnitude input) (work d.idx.castSucc) ∧
    (work d.sign.castSucc).read = Γ.ofBool (SignedRawControl.negative input) ∧
    BoundedOccurrenceMachine.Loaded d.Physical d.ending.castSucc d.flag.castSucc (SignedRawControl.rest input) work

theorem bound_source_mono (b L C : ℕ) (hb : b ≤ L) :
    OffsetTemplateProgram.bound 16 b C ≤ OffsetTemplateProgram.bound 16 L C := by
  have hp := Nat.mul_le_mul_left 16 (Nat.add_le_add_right hb 2609)
  have hi := Nat.add_le_add_right (Nat.add_le_add
    (Nat.mul_le_mul_left 13 (Nat.add_le_add_left hp C)) (Nat.mul_le_mul_left 54 hb)) 138381
  exact Nat.mul_le_mul_left 16 hi

theorem hoareTime (boxed : Bool) (d : Layout w) (L A C : ℕ) (before input emitted : List Bool)
    (hlen : input.length ≤ L) (hA : A.bits.length ≤ C)
    (R : (Fin w → Tape) → Prop) (hR : SparseOffsetLayout.Stable d R) :
    (machine boxed d).HoareTime (Inv L d A before input emitted R)
      (Post L boxed d A before input emitted R) (75 * L + 126 + OffsetTemplateProgram.bound 16 L C) := by
  let S : (Fin (w + 1) → Tape) → Prop := fun work =>
    (work d.adjusted.castSucc).head = 1 ∧ Register A (work d.acc.castSucc) ∧
    Empty (work d.aux.castSucc) ∧ Empty (work (Fin.last w)) ∧ R (oldWork work)
  have hS : ∀ work next, (∀ j, j ≠ d.idx.castSucc → j ≠ d.sign.castSucc → ¬d.Touches j → next j = work j) →
      S work → S next := by
    rintro work next he ⟨hh, ha, hu, hl, hx⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [he d.adjusted.castSucc
        (TemplateFactorPipeline.cast_ne _ _ d.arithmetic_sep.idx_adjusted.symm)
        (TemplateFactorPipeline.cast_ne _ _ d.arithmetic_sep.sign_adjusted.symm) d.adjusted_outside]
      exact hh
    · rw [he d.acc.castSucc (TemplateFactorPipeline.cast_ne _ _ d.arithmetic_sep.idx_acc.symm)
        (TemplateFactorPipeline.cast_ne _ _ d.arithmetic_sep.sign_acc.symm) d.acc_outside]
      exact ha
    · rw [he d.aux.castSucc (TemplateFactorPipeline.cast_ne _ _ d.arithmetic_sep.idx_aux.symm)
        (TemplateFactorPipeline.cast_ne _ _ d.arithmetic_sep.sign_aux.symm) d.aux_outside]
      exact hu
    · rw [he (Fin.last w) (cast_ne_last d.idx).symm (cast_ne_last d.sign).symm d.last_untouched]
      exact hl
    · exact hR (oldWork work) (oldWork next) (fun j hji hjs hjt _ _ _ =>
        he j.castSucc (TemplateFactorPipeline.cast_ne _ _ hji) (TemplateFactorPipeline.cast_ne _ _ hjs) hjt) hx
  let T : (Fin w → Tape) → Prop := fun work =>
    SparseOffsetLayout.Ready L d work ∧ SparseOffsetLayout.Loaded d (SignedRawControl.rest input) work ∧ R work
  have hT : OffsetContribution.Stable d.adjusted d.acc d.aux T := by
    rintro work next he ⟨hr, hl, hx⟩
    exact ⟨SparseOffsetLayout.ready_stable L d work next he hr,
      SparseOffsetLayout.loaded_stable d (SignedRawControl.rest input) work next he hl,
      hR work next (fun j _ _ _ hja hjc hju => he j hja hjc hju) hx⟩
  have hs := SparseTermCanonicalLoad.four_hoareTime d.Physical d.ending.castSucc d.flag.castSucc d.idx.castSucc d.sign.castSucc
    (SparseOffsetLayout.physical_length d) d.parse_sep L before input emitted hlen S hS
  have ht := OffsetTemplateDispatch.hoareTime boxed (SignedRawControl.negative input) (SignedRawControl.magnitude input) A C
    d.Physical d.ending.castSucc d.flag.castSucc (SparseOffsetLayout.physical_length d) (SignedRawControl.rest input)
    d.idx d.sign d.adjusted d.acc d.aux d.arithmetic_sep hA
    (before ++ SparseTermOffsetControl.taken input) (SparseTermOffsetControl.rest input) emitted T hT
  have hf := seqTM_hoareTime _ _ hs (by
    rintro inp work out ⟨hc, hsafe, hreusable, hv, hsh, hread, hrefs, hloaded, hh, ha, hu, hl, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    have hc' : Cursor (before ++ SparseTermOffsetControl.taken input) (SparseTermOffsetControl.rest input) emitted inp work out := by
      simpa only [SparseOffsetLayout.physical_length d, SparseTermOffsetControl.taken, SparseTermOffsetControl.rest] using hc
    have hready := SparseOffsetLayout.ready_from_parts L d work hreusable hsh hrefs
    have hloaded' := (SparseOffsetLayout.loaded_iff d (SignedRawControl.rest input) work).mpr hloaded
    exact ⟨⟨hc', hsafe, hv, hread, hh, ha, hu, hl, hready, hloaded', hx⟩, hloaded⟩) ht
  apply hf.consequence
  · rintro inp work out ⟨hc, hs, hready, hh, ha, hu, hl, hx⟩
    have hp := SparseOffsetLayout.ready_parts L d work hready
    exact ⟨hc, hs, hp.1, hp.2.1, hp.2.2, hh, ha, hu, hl, hx⟩
  · rintro inp work out ⟨hc, hs, hv, hread, hh, ha, hu, hl, hready, hloaded, hx⟩
    have ha' : Register (A + SparseTermOffsetControl.delta boxed input) (work d.acc.castSucc) := by
      simpa only [SparseTermOffsetControl.delta, SparseTermOffsetControl.choice, SparseOffsetLayout.physical_length d] using ha
    exact ⟨⟨hc, hs, hready, hh, ha', hu, hl, hx⟩, hv, hread,
      (SparseOffsetLayout.loaded_iff d (SignedRawControl.rest input) work).mp hloaded⟩
  · have hm := (SignedRawControl.magnitude_bits_length input).trans hlen
    have hb := bound_source_mono (SignedRawControl.magnitude input).bits.length L C hm
    omega

end JointThermoComplexity.Complexity.SparseTermOffsetBody

#print axioms JointThermoComplexity.Complexity.SparseTermOffsetBody.machine
#print axioms JointThermoComplexity.Complexity.SparseTermOffsetBody.hoareTime
