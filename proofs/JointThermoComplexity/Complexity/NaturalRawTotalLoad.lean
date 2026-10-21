module
public import proofs.JointThermoComplexity.Complexity.NaturalRawTotalRun
public import proofs.JointThermoComplexity.Complexity.NaturalRawLoad

set_option autoImplicit false
@[expose] public section

/-! Total loading into the existing raw-natural work-buffer machine. Runtime
depends on input length, and canonical fields recover exactly Nat.bits.
-/

namespace JointThermoComplexity.Complexity.NaturalRawTotalLoad
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState BoxFieldLoad
variable {w : ℕ}

theorem copy_hoareTime (idx : Fin (w + 1)) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (NaturalRawLoad.copyMachine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix [] ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor (before ++ (NaturalRawControl.scan input).taken) (NaturalRawControl.scan input).rest emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryPrefix (NaturalRawControl.scan input).bits ∧
        (work idx).cells 0 = Γ.start ∧ R work) (input.length + 1) := by
  have h := TransducedBufferAt.hoareTime (permutation idx) NaturalRawMachine.machine
    (NaturalRawControl.scan input).taken (NaturalRawControl.scan input).bits before (NaturalRawControl.scan input).rest emitted
    (input.length + 1) (fun C => by
      simpa only [NaturalRawControl.split, List.nil_append] using NaturalRawTotalRun.hoareTime input before [] C)
    R (by simpa only [destination] using hR)
  simpa only [NaturalRawLoad.copyMachine, destination, NaturalRawControl.split] using h

theorem exact_hoareTime (idx : Fin (w + 1)) (old before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (NaturalRawLoad.machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryContent old ∧ (work idx).cells 0 = Γ.start ∧ (work idx).head ≤ old.length + 1 ∧ R work)
      (fun inp work out => Cursor (before ++ (NaturalRawControl.scan input).taken) (NaturalRawControl.scan input).rest emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString (NaturalRawControl.scan input).bits ∧
        (work idx).cells 0 = Γ.start ∧ R work) (3 * old.length + 2 * input.length + 20) := by
  have hr := BinaryBufferReset.hoareTime idx old before input emitted R hR
  have hc := copy_hoareTime idx before input emitted R hR
  have hw := BinaryPrefixRewind.hoareTime idx (NaturalRawControl.scan input).bits
    (before ++ (NaturalRawControl.scan input).taken) (NaturalRawControl.scan input).rest emitted R hR
  have hrc := seqTM_hoareTime (BinaryBufferReset.machine idx) (NaturalRawLoad.copyMachine idx) hr (by
    rintro inp work out ⟨hc, hs, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, CountTape.empty_prefix_of_zero hz, hz.cell0, hr⟩) hc
  have hfull := seqTM_hoareTime (seqTM (BinaryBufferReset.machine idx) (NaturalRawLoad.copyMachine idx))
    (rewindWorkTM idx) hrc (by
      rintro inp work out ⟨hc, hs, hb, hz, hr⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hs, hb, hz, hr⟩) hw
  exact hfull.consequence (fun _ _ _ h => h) (fun _ _ _ h => h)
    (by have := NaturalRawControl.bits_length input; omega)

theorem hoareTime (L : ℕ) (idx : Fin (w + 1)) (before input emitted : List Bool) (hlen : input.length ≤ L)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (NaturalRawLoad.machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ R work)
      (fun inp work out => Cursor (before ++ (NaturalRawControl.scan input).taken) (NaturalRawControl.scan input).rest emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString (NaturalRawControl.scan input).bits ∧
        (work idx).cells 0 = Γ.start ∧ Reusable L (work idx) ∧ R work) (14 * L + 20) := by
  rintro inp work out ⟨hc, hs, ⟨old, hold, hcontent, hz, hhead⟩, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', hb', hz', hr'⟩ :=
    exact_hoareTime idx old before input emitted R hR inp work out ⟨hc, hs, hcontent, hz, hhead, hr⟩
  have hbits : (NaturalRawControl.scan input).bits.length ≤ L := (NaturalRawControl.bits_length input).trans hlen
  have hreusable : Reusable L (d.work idx) :=
    ⟨(NaturalRawControl.scan input).bits, by omega, hb'.2, hz', by rw [hb'.1]; omega⟩
  exact ⟨d, t, by omega, hd, hh, hc', hs', hb', hz', hreusable, hr'⟩

theorem natural_hoareTime (L : ℕ) (idx : Fin (w + 1)) (value : ℕ) (before suffix emitted : List Bool)
    (hlen : (BitCodec.naturalCode value ++ suffix).length ≤ L) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (NaturalRawLoad.machine idx).HoareTime
      (fun inp work out => Cursor before (BitCodec.naturalCode value ++ suffix) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ Reusable L (work idx) ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.naturalCode value) suffix emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString value.bits ∧ (work idx).cells 0 = Γ.start ∧
        Reusable L (work idx) ∧ R work) (14 * L + 20) := by
  simpa only [NaturalRawControl.natural] using hoareTime L idx before (BitCodec.naturalCode value ++ suffix) emitted hlen R hR

end JointThermoComplexity.Complexity.NaturalRawTotalLoad

#print axioms JointThermoComplexity.Complexity.NaturalRawTotalLoad.copy_hoareTime
#print axioms JointThermoComplexity.Complexity.NaturalRawTotalLoad.exact_hoareTime
#print axioms JointThermoComplexity.Complexity.NaturalRawTotalLoad.hoareTime
#print axioms JointThermoComplexity.Complexity.NaturalRawTotalLoad.natural_hoareTime
