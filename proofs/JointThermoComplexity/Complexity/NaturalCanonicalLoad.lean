module
public import proofs.JointThermoComplexity.Complexity.NaturalRawTotalLoad
public import proofs.JointThermoComplexity.Complexity.BinaryTrimRuntime
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementRun

set_option autoImplicit false
@[expose] public section

/-! Total raw-field loading followed by high-zero erasure. Every finite input
produces a canonical magnitude register, not just already canonical fields. -/

namespace JointThermoComplexity.Complexity.NaturalCanonicalLoad
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
variable {w : ℕ}

def value (input : List Bool) : ℕ := BitCodec.readBits (NaturalRawControl.scan input).bits

def machine (idx : Fin (w + 1)) : TM (w + 1) :=
  seqTM (seqTM (seqTM (BinaryBufferReset.machine idx) (NaturalRawLoad.copyMachine idx))
    (BinaryTrimMachine.machine idx)) (rewindWorkTM idx)

theorem bits_length (input : List Bool) : (value input).bits.length ≤ input.length := by
  rw [value, ← BinaryTrim.canonical]
  exact (BinaryTrim.length_le _).trans (NaturalRawControl.bits_length input)

theorem exact_hoareTime (idx : Fin (w + 1)) (old before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ idx → next j = work j) → R work → R next) :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryContent old ∧ (work idx).cells 0 = Γ.start ∧
        (work idx).head ≤ old.length + 1 ∧ R work)
      (fun inp work out => Cursor (before ++ (NaturalRawControl.scan input).taken) (NaturalRawControl.scan input).rest emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register (value input) (work idx) ∧ R work)
      (3 * old.length + 3 * input.length + 18) := by
  have hr := BinaryBufferReset.hoareTime idx old before input emitted R hR
  have hc := NaturalRawTotalLoad.copy_hoareTime idx before input emitted R hR
  have ht := BinaryTrimRuntime.canonical_hoareTime idx (NaturalRawControl.scan input).bits
    (before ++ (NaturalRawControl.scan input).taken) (NaturalRawControl.scan input).rest emitted R hR
  have hw := BinaryPrefixRewind.hoareTime idx (value input).bits
    (before ++ (NaturalRawControl.scan input).taken) (NaturalRawControl.scan input).rest emitted R hR
  have hrc := seqTM_hoareTime _ _ hr (by
    rintro inp work out ⟨hc, hs, hz, hx⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, CountTape.empty_prefix_of_zero hz, hz.cell0, hx⟩) hc
  have hrct := seqTM_hoareTime _ _ hrc (by
    rintro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.phase
    rw [hi, hw, ho]
    exact hp) ht
  have hfull := seqTM_hoareTime _ _ hrct (by
    rintro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.phase
    rw [hi, hw, ho]
    exact hp) hw
  apply hfull.consequence (fun _ _ _ hp => hp)
  · rintro inp work out ⟨hc, hs, hb, hz, hx⟩
    exact ⟨hc, hs, ⟨hb, hz⟩, hx⟩
  · have hb := NaturalRawControl.bits_length input
    have hv := bits_length input
    omega

theorem hoareTime (L : ℕ) (idx : Fin (w + 1)) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ idx → next j = work j) → R work → R next) :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ R work)
      (fun inp work out => Cursor (before ++ (NaturalRawControl.scan input).taken) (NaturalRawControl.scan input).rest emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register (value input) (work idx) ∧ Reusable L (work idx) ∧ R work)
      (15 * L + 18) := by
  rintro inp work out ⟨hc, hs, ⟨old, hold, hb, hz, hh⟩, hx⟩
  obtain ⟨d, t, ht, hd, hdhalt, hc', hs', hv, hx'⟩ :=
    exact_hoareTime idx old before input emitted R hR inp work out ⟨hc, hs, hb, hz, hh, hx⟩
  have hbits : (value input).bits.length ≤ L := (bits_length input).trans hlen
  have hreusable : Reusable L (d.work idx) :=
    ⟨(value input).bits, by omega, hv.1.2, hv.2, by rw [hv.1.1]; omega⟩
  exact ⟨d, t, by omega, hd, hdhalt, hc', hs', hv, hreusable, hx'⟩

theorem natural_hoareTime (L : ℕ) (idx : Fin (w + 1)) (v : ℕ) (before suffix emitted : List Bool)
    (hlen : (BitCodec.naturalCode v ++ suffix).length ≤ L) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work next, (∀ j, j ≠ idx → next j = work j) → R work → R next) :
    (machine idx).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode v ++ suffix) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode v) suffix emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ BinaryIncrementRun.Register v (work idx) ∧ Reusable L (work idx) ∧ R work)
      (15 * L + 18) := by
  simpa only [value, NaturalRawControl.natural, BitCodec.readBits_bits] using
    hoareTime L idx before (BitCodec.naturalCode v ++ suffix) emitted hlen R hR

end JointThermoComplexity.Complexity.NaturalCanonicalLoad

#print axioms JointThermoComplexity.Complexity.NaturalCanonicalLoad.machine
#print axioms JointThermoComplexity.Complexity.NaturalCanonicalLoad.hoareTime
#print axioms JointThermoComplexity.Complexity.NaturalCanonicalLoad.natural_hoareTime
