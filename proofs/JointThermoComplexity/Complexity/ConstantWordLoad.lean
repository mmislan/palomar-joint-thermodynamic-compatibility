module
public import proofs.JointThermoComplexity.Complexity.BoxFieldLoad
public import proofs.JointThermoComplexity.Complexity.BinaryPrefixRewind
public import proofs.JointThermoComplexity.Complexity.TransducedBufferAt

set_option autoImplicit false
@[expose] public section

/-! Store a fixed literal word without consuming real input or emitting real
output. Virtual output routing preserves all other physical work tapes.
-/

namespace JointThermoComplexity.Complexity.ConstantWordLoad
open _root_.Complexity _root_.Complexity.TM BoxBufferState BoxFieldLoad
open HeaderAt (Cursor)
variable {w : ℕ}

def copyMachine (idx : Fin (w + 1)) (bits : List Bool) : TM (w + 1) :=
  TransducedBufferAt.machine (permutation idx) (emitBitsTM bits)

theorem copy_hoareTime (idx : Fin (w + 1)) (bits before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (copyMachine idx bits).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix [] ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix bits ∧ (work idx).cells 0 = Γ.start ∧ R work) bits.length := by
  rintro inp work out ⟨hc, hs, hp, hz, hr⟩
  let e := permutation idx
  have hport : e (Fin.last w) = idx := Equiv.swap_apply_left _ _
  have hdest : CountSumAt.destination e = idx := destination idx
  let original : Fin w → Tape := fun j => work (e j.castSucc)
  have hbase := OutputRoute.hoareTime (emitBitsTM (n := w) bits) _ _ bits.length (fun out' => out' = out)
    (FixedOutput.hoareTime bits before input [] (fun old => old = original))
  have hroute := WorkPermutation.hoareTime e (emitBitsTM (n := w) bits).retargetOutput _ _ bits.length hbase
  have hcur : Cursor before input [] inp original (work idx) :=
    ⟨hc.cells, hc.head, (fun j => hc.works (e j.castSucc)), hp, hz⟩
  obtain ⟨d, time, ht, hd, hh, _, hdout, hdcur, _, hdold⟩ :=
    hroute inp work out ⟨hc.output_read, rfl, by simpa only [hport, original] using hcur,
      (fun j => hs (e j.castSucc)), rfl⟩
  have he : ∀ j, j ≠ idx → d.work j = work j := by
    intro j hj
    obtain ⟨k, hk⟩ := CountSumAt.preimage e j (by simpa only [hdest] using hj)
    have h := congrArg (fun f : Fin w → Tape => f k) hdold
    change d.work (e k.castSucc) = work (e k.castSucc) at h
    simpa only [hk] using h
  have hb : (d.work idx).HasBinaryPrefix bits := by
    simpa only [hport, List.nil_append] using hdcur.tapePrefix
  have hsafe : ∀ j, Parked (d.work j) := by
    intro j
    by_cases hj : j = idx
    · subst j
      exact ⟨by rw [hb.1]; omega, (show (d.work idx).HasBinaryContent bits from hb.2).cells_ne_start⟩
    · rw [he j hj]
      exact hs j
  have hcursor : Cursor before input emitted d.input d.work d.output :=
    ⟨hdcur.cells, hdcur.head, (fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩),
      by simpa only [hdout] using hc.tapePrefix, by simpa only [hdout] using hc.zero⟩
  exact ⟨d, time, ht, hd, hh, hcursor, hsafe, hb, by simpa only [hport] using hdcur.zero,
    hR work d.work he hr⟩

def machine (idx : Fin (w + 1)) (bits : List Bool) : TM (w + 1) :=
  seqTM (seqTM (BinaryBufferReset.machine idx) (copyMachine idx bits)) (rewindWorkTM idx)

theorem exact_hoareTime (idx : Fin (w + 1)) (old bits before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx bits).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryContent old ∧ (work idx).cells 0 = Γ.start ∧ (work idx).head ≤ old.length + 1 ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (3 * old.length + 2 * bits.length + 14) := by
  have hr := BinaryBufferReset.hoareTime idx old before input emitted R hR
  have hc := copy_hoareTime idx bits before input emitted R hR
  have hw := BinaryPrefixRewind.hoareTime idx bits before input emitted R hR
  have hrc := seqTM_hoareTime _ _ hr (by
    rintro inp work out ⟨hc, hs, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, CountTape.empty_prefix_of_zero hz, hz.cell0, hr⟩) hc
  have h := seqTM_hoareTime _ _ hrc (by
    rintro inp work out ⟨hc, hs, hb, hz, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hs, hb, hz, hr⟩) hw
  exact h.mono_bound (by omega)

theorem hoareTime (B : ℕ) (idx : Fin (w + 1)) (bits before input emitted : List Bool) (hbits : bits.length ≤ 4 * B)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx bits).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Reusable B (work idx) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryString bits ∧ (work idx).cells 0 = Γ.start ∧ Reusable B (work idx) ∧ R work) (20 * B + 14) := by
  rintro inp work out ⟨hc, hs, ⟨old, hold, hb, hz, hh⟩, hr⟩
  obtain ⟨d, time, ht, hd, halt, hc', hs', hb', hz', hr'⟩ :=
    exact_hoareTime idx old bits before input emitted R hR inp work out ⟨hc, hs, hb, hz, hh, hr⟩
  exact ⟨d, time, by omega, hd, halt, hc', hs', hb', hz',
    ⟨bits, hbits, hb'.2, hz', by rw [hb'.1]; omega⟩, hr'⟩

end JointThermoComplexity.Complexity.ConstantWordLoad

#print axioms JointThermoComplexity.Complexity.ConstantWordLoad.copy_hoareTime
#print axioms JointThermoComplexity.Complexity.ConstantWordLoad.hoareTime
