module
public import proofs.JointThermoComplexity.Complexity.BinaryAddRun
public import proofs.JointThermoComplexity.Complexity.BinaryScaleBuffer
public import proofs.JointThermoComplexity.Complexity.BinaryTrimRuntime

set_option autoImplicit false
@[expose] public section

/-! Route the raw sum into a separate work tape, trim high zeros and rewind.
The result is a canonical sum register and the original work data survive. -/

namespace JointThermoComplexity.Complexity.BinaryAddBuffer
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open BinaryScaleBuffer (oldWork cast_ne_last)
variable {w : ℕ}

def rawMachine (left right : Fin w) : TM (w + 1) := (BinaryAddRun.machine left right).retargetOutput

def machine (left right : Fin w) : TM (w + 1) :=
  seqTM (seqTM (rawMachine left right) (BinaryTrimMachine.machine (Fin.last w))) (rewindWorkTM (Fin.last w))

theorem sum_bits_length (m n : ℕ) : (m + n).bits.length ≤ m.bits.length + n.bits.length + 1 := by
  have h := BinaryTrim.length_le (BinaryAddControl.add false m.bits n.bits)
  rw [BinaryAddControl.canonical_sum] at h
  exact h.trans (BinaryAddControl.length_add false m.bits n.bits)

theorem raw_hoareTime (left right : Fin w) (hne : left ≠ right) (m n : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (rawMachine left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register m (work left.castSucc) ∧ Register n (work right.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register m (work left.castSucc) ∧ Register n (work right.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix (BinaryAddControl.add false m.bits n.bits) ∧
        (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (2 * (m.bits.length + n.bits.length) + 9) := by
  have h := BinaryAddRun.natural_hoareTime left right hne m n before input [] R
  have hr := OutputRoute.hoareTime (BinaryAddRun.machine left right) _ _ _
    (fun out => out.HasBinaryPrefix emitted ∧ out.cells 0 = Γ.start) h
  apply hr.consequence
  · rintro inp work out ⟨hc, hs, hl, hr, hb, hz, hx⟩
    exact ⟨hc.output_read, ⟨hc.tapePrefix, hc.zero⟩,
      ⟨hc.cells, hc.head, fun j => hc.works j.castSucc, hb, hz⟩,
      (fun j => hs j.castSucc), hl, hr, hx⟩
  · rintro inp work out ⟨_, ⟨ho, hoz⟩, hc, hs, hl, hr, hx⟩
    have hb : (work (Fin.last w)).HasBinaryPrefix (BinaryAddControl.add false m.bits n.bits) :=
      by simpa only [List.nil_append] using hc.tapePrefix
    have hcontent : (work (Fin.last w)).HasBinaryContent (BinaryAddControl.add false m.bits n.bits) := hb.2
    have hsafe : ∀ j, Parked (work j) := by
      intro j
      refine Fin.lastCases ?_ (fun i => hs i) j
      exact ⟨by rw [hb.1]; omega, hcontent.cells_ne_start⟩
    exact ⟨⟨hc.cells, hc.head, fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩, ho, hoz⟩,
      hsafe, hl, hr, hb, hc.zero, hx⟩
  · exact le_rfl

theorem natural_hoareTime (left right : Fin w) (hne : left ≠ right) (m n : ℕ)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register m (work left.castSucc) ∧ Register n (work right.castSucc) ∧
        (work (Fin.last w)).HasBinaryPrefix [] ∧ (work (Fin.last w)).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register m (work left.castSucc) ∧ Register n (work right.castSucc) ∧
        Register (m + n) (work (Fin.last w)) ∧ R (oldWork work))
      (4 * (m.bits.length + n.bits.length) + 18) := by
  let S : (Fin (w + 1) → Tape) → Prop := fun work =>
    Register m (work left.castSucc) ∧ Register n (work right.castSucc) ∧ R (oldWork work)
  have hS : ∀ work next, (∀ j, j ≠ Fin.last w → next j = work j) → S work → S next := by
    rintro work next he ⟨hl, hr, hx⟩
    have hold : oldWork next = oldWork work := funext (fun j => he j.castSucc (cast_ne_last j))
    exact ⟨by rw [he left.castSucc (cast_ne_last left)]; exact hl,
      by rw [he right.castSucc (cast_ne_last right)]; exact hr,
      by rw [hold]; exact hx⟩
  have hsum : BitCodec.readBits (BinaryAddControl.add false m.bits n.bits) = m + n := by
    rw [BinaryAddControl.read_add, BitCodec.readBits_bits, BitCodec.readBits_bits]
    simp [BinaryAddControl.val]
  have hb := raw_hoareTime left right hne m n before input emitted R
  have ht := BinaryTrimRuntime.canonical_hoareTime (Fin.last w) (BinaryAddControl.add false m.bits n.bits)
    before input emitted S hS
  rw [hsum] at ht
  have hw := BinaryPrefixRewind.hoareTime (Fin.last w) (m + n).bits before input emitted S hS
  have hbt := seqTM_hoareTime _ _ hb (by
    rintro inp work out ⟨hc, hs, hl, hr, hp, hz, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hp, hz, hl, hr, hx⟩) ht
  have hf := seqTM_hoareTime _ _ hbt (by
    rintro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.phase
    rw [hi, hw, ho]
    exact hp) hw
  apply hf.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hc, hs, hb, hz, hl, hr, hx⟩
    exact ⟨hc, hs, hl, hr, ⟨hb, hz⟩, hx⟩
  · have hraw := BinaryAddControl.length_add false m.bits n.bits
    have hcanonical := sum_bits_length m n
    omega

end JointThermoComplexity.Complexity.BinaryAddBuffer

#print axioms JointThermoComplexity.Complexity.BinaryAddBuffer.machine
#print axioms JointThermoComplexity.Complexity.BinaryAddBuffer.raw_hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryAddBuffer.natural_hoareTime
