module
public import proofs.JointThermoComplexity.Complexity.CountedSparseFrame
public import proofs.JointThermoComplexity.Complexity.NormalizedCountDispatch

set_option autoImplicit false
@[expose] public section

/-! A complete term updates both its fixed offset and normalized-row count. -/

namespace JointThermoComplexity.Complexity.CountedSparseTermBody
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork)
open SparseOffsetPorts

def machine (boxed : Bool) : TM 33 := seqTM (SparseTermOffsetBody.machine boxed layout)
  (NormalizedCountDispatch.machine layout.Physical layout.ending.castSucc layout.flag.castSucc rows.castSucc)

def Pre (L A N : ℕ) (before input emitted : List Bool) (R : (Fin 32 → Tape) → Prop) :
    _root_.Complexity.TM.TapePred 33 := fun inp work out =>
  SparseTermOffsetBody.Inv L layout A before input emitted R inp work out ∧ Register N (work rows.castSucc)

def Post (L : ℕ) (boxed : Bool) (A N : ℕ) (before input emitted : List Bool)
    (R : (Fin 32 → Tape) → Prop) : _root_.Complexity.TM.TapePred 33 := fun inp work out =>
  SparseTermOffsetBody.Post L boxed layout A before input emitted R inp work out ∧
    Register (N + SparseTermOffsetControl.count input) (work rows.castSucc)

theorem count_bits (input : List Bool) (N : ℕ) :
    (N + SparseTermOffsetControl.count input).bits.length ≤ N.bits.length + 16 := by
  exact (BinaryConstantAdd.bits_add N _).trans (Nat.add_le_add_left (SparseTermOffsetControl.count_le input) _)

theorem hoareTime (boxed : Bool) (L A C N B : ℕ) (before input emitted : List Bool)
    (hlen : input.length ≤ L) (hA : A.bits.length ≤ C) (hN : N.bits.length ≤ B)
    (R : (Fin 32 → Tape) → Prop) (hR : SparseOffsetLayout.Stable layout R) (hRow : CountedSparseFrame.Stable R) :
    (machine boxed).HoareTime (Pre L A N before input emitted R) (Post L boxed A N before input emitted R)
      (75 * L + 726 + OffsetTemplateProgram.bound 16 L C + 32 * B) := by
  let S : (Fin 32 → Tape) → Prop := fun work => R work ∧ Register N (work rows)
  have hS : SparseOffsetLayout.Stable layout S := by
    rintro work next he ⟨hr, hn⟩
    exact ⟨hR work next he hr, CountedSparseFrame.row_stable N work next he hn⟩
  let A' := A + SparseTermOffsetControl.delta boxed input
  let raw := SignedRawControl.rest input
  let T : (Fin 33 → Tape) → Prop := fun work => SparseTermOffsetBody.Fields L layout A' R work ∧
    Register (SignedRawControl.magnitude input) (work layout.idx.castSucc) ∧
    (work layout.sign.castSucc).read = Γ.ofBool (SignedRawControl.negative input) ∧
    BoundedOccurrenceMachine.Loaded layout.Physical layout.ending.castSucc layout.flag.castSucc raw work
  have hT : BinaryIncrementFramed.Stable rows.castSucc T := by
    rintro work next he ⟨hf, hv, hs, hl⟩
    exact ⟨CountedSparseFrame.fields_stable L A' R hRow work next he hf,
      by rw [he layout.idx.castSucc (by decide)]; exact hv,
      by rw [he layout.sign.castSucc (by decide)]; exact hs,
      CountedSparseFrame.loaded_stable raw work next he hl⟩
  have hs := SparseTermOffsetBody.hoareTime boxed layout L A C before input emitted hlen hA S hS
  have ht := NormalizedCountDispatch.hoareTime layout.Physical layout.ending.castSucc layout.flag.castSucc rows.castSucc
    (SparseOffsetLayout.physical_length layout) raw N B hN
    (before ++ SparseTermOffsetControl.taken input) (SparseTermOffsetControl.rest input) emitted T hT
  have hf := seqTM_hoareTime _ _ hs (by
    rintro inp work out ⟨⟨hc, hsafe, hready, hh, ha, hu, hl, hr, hn⟩, hv, hsign, hloaded⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, hsafe, hn, ⟨hready, hh, ha, hu, hl, hr⟩, hv, hsign, hloaded⟩, hloaded⟩) ht
  apply hf.consequence
  · rintro inp work out ⟨⟨hc, hsafe, hready, hh, ha, hu, hl, hr⟩, hn⟩
    exact ⟨hc, hsafe, hready, hh, ha, hu, hl, hr, hn⟩
  · rintro inp work out ⟨hc, hsafe, hn, hf, hv, hsign, hloaded⟩
    exact ⟨⟨⟨hc, hsafe, hf⟩, hv, hsign, hloaded⟩, hn⟩
  · omega

end JointThermoComplexity.Complexity.CountedSparseTermBody

#print axioms JointThermoComplexity.Complexity.CountedSparseTermBody.machine
#print axioms JointThermoComplexity.Complexity.CountedSparseTermBody.hoareTime
