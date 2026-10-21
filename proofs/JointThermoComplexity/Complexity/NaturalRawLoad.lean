module
public import proofs.JointThermoComplexity.Complexity.TransducedBufferAt
public import proofs.JointThermoComplexity.Complexity.NaturalRawCopy
public import proofs.JointThermoComplexity.Complexity.BoxFieldLoad
public import proofs.JointThermoComplexity.Complexity.BinaryPrefixRewind

set_option autoImplicit false
@[expose] public section

/-! Replace one bounded work buffer by the actual canonical Nat.bits payload and rewind it for arithmetic. -/

namespace JointThermoComplexity.Complexity.NaturalRawLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxBufferState BoxFieldLoad

variable {w : ℕ}

def copyMachine (idx : Fin (w + 1)) : TM (w + 1) :=
  TransducedBufferAt.machine (permutation idx) NaturalRawMachine.machine

theorem copy_hoareTime (idx : Fin (w + 1)) (value : ℕ) (before tail emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (copyMachine idx).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix [] ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix value.bits ∧ (work idx).cells 0 = Γ.start ∧ R work) (2 * value.bits.length + 1) := by
  have hs := TransducedBufferAt.hoareTime (permutation idx) NaturalRawMachine.machine
    (BitCodec.naturalCode value) value.bits before tail emitted (2 * value.bits.length + 1)
    (fun C => by simpa only [List.nil_append] using NaturalRawCopy.natural_hoareTime value before tail [] C) R
    (by simpa only [destination] using hR)
  simpa only [copyMachine, destination] using hs

def machine (idx : Fin (w + 1)) : TM (w + 1) :=
  seqTM (seqTM (BinaryBufferReset.machine idx) (copyMachine idx)) (rewindWorkTM idx)

theorem exact_hoareTime (idx : Fin (w + 1)) (old : List Bool) (value : ℕ) (before tail emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryContent old ∧ (work idx).cells 0 = Γ.start ∧ (work idx).head ≤ old.length + 1 ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryString value.bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (3 * old.length + 3 * value.bits.length + 15) := by
  have hr := BinaryBufferReset.hoareTime idx old before (BitCodec.naturalCode value ++ tail) emitted R hR
  have hc := copy_hoareTime idx value before tail emitted R hR
  have hw := BinaryPrefixRewind.hoareTime idx value.bits (before ++ BitCodec.naturalCode value) tail emitted R hR
  have hrc := seqTM_hoareTime (BinaryBufferReset.machine idx) (copyMachine idx) hr (by
    rintro inp work out ⟨hc, hs, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, CountTape.empty_prefix_of_zero hz, hz.cell0, hr⟩) hc
  have hfull := seqTM_hoareTime (seqTM (BinaryBufferReset.machine idx) (copyMachine idx)) (rewindWorkTM idx) hrc (by
    rintro inp work out ⟨hc, hs, hb, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hb, hz, hr⟩) hw
  exact hfull.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by omega)

theorem hoareTime (L : ℕ) (idx : Fin (w + 1)) (value : ℕ) (hlen : (BitCodec.naturalCode value).length ≤ L)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ tail) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Reusable L (work idx) ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) tail emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryString value.bits ∧ (work idx).cells 0 = Γ.start ∧ Reusable L (work idx) ∧ R work) (15 * L + 15) := by
  rintro inp work out ⟨hc, hs, ⟨old, hold, hcontent, hz, hhead⟩, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', hb', hz', hr'⟩ := exact_hoareTime idx old value before tail emitted R hR
    inp work out ⟨hc, hs, hcontent, hz, hhead, hr⟩
  have hbits : value.bits.length ≤ L := by rw [BitCodec.naturalCode_length] at hlen; omega
  have hreusable : Reusable L (d.work idx) := ⟨value.bits, by omega, hb'.2, hz', by rw [hb'.1]; omega⟩
  exact ⟨d, t, by omega, hd, hh, hc', hs', hb', hz', hreusable, hr'⟩

end JointThermoComplexity.Complexity.NaturalRawLoad

#print axioms JointThermoComplexity.Complexity.NaturalRawLoad.exact_hoareTime
#print axioms JointThermoComplexity.Complexity.NaturalRawLoad.hoareTime
