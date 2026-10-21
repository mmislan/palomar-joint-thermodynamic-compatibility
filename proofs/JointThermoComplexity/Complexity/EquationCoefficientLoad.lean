module
public import proofs.JointThermoComplexity.Complexity.EquationCoefficientRun
public import proofs.JointThermoComplexity.Complexity.TransducedBufferAt
public import proofs.JointThermoComplexity.Complexity.BoxFieldLoad
public import proofs.JointThermoComplexity.Complexity.BinaryPrefixRewind

set_option autoImplicit false
@[expose] public section

/-! Store a bounded signed equation coefficient in a reusable physical work
buffer while retaining the real output and every other work tape.
-/

namespace JointThermoComplexity.Complexity.EquationCoefficientLoad
open _root_.Complexity _root_.Complexity.TM HeaderAt BoxBufferState
variable {w : ℕ}

def output (input : List Bool) : List Bool := BitCodec.integerCode (EquationCoefficientControl.signedValue input)

theorem output_length (input : List Bool) : (output input).length ≤ 8 := by
  have h := EquationCoefficientControl.word_bound false (EquationCoefficientControl.signed input).1
    (EquationCoefficientControl.signed input).2.magnitude
  simpa [EquationCoefficientControl.signed_word, output] using h

def routedMachine (e : Fin (w + 1) ≃ Fin (w + 1)) : TM (w + 1) :=
  TransducedBufferAt.machine e (EquationCoefficientMachine.machine false w)

theorem routed_hoareTime (e : Fin (w + 1) ≃ Fin (w + 1)) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ CountSumAt.destination e → work' j = work j) → R work → R work') :
    (routedMachine e).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work (CountSumAt.destination e)).HasBinaryPrefix [] ∧ (work (CountSumAt.destination e)).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work (CountSumAt.destination e)).HasBinaryPrefix (output input) ∧
        (work (CountSumAt.destination e)).cells 0 = Γ.start ∧ R work) (input.length + 11) := by
  rintro inp work out ⟨hc, hs, hp, hz, hr⟩
  let original : Fin w → Tape := fun j => work (e j.castSucc)
  have hcopy := EquationCoefficientRun.hoareTime false before input [] (fun old => old = original)
  have hbase := OutputRoute.hoareTime (EquationCoefficientMachine.machine false w) _ _ (input.length + 11)
    (fun out' => out' = out) hcopy
  have hroute := WorkPermutation.hoareTime e (EquationCoefficientMachine.machine false w).retargetOutput _ _
    (input.length + 11) hbase
  obtain ⟨d, t, ht, hreach, hhalt, _, hdout, hdcur, _, hdold⟩ := hroute inp work out
    ⟨hc.output_read, rfl, ⟨hc.cells, hc.head, fun j => hc.works (e j.castSucc), hp, hz⟩,
      (fun j => hs (e j.castSucc)), rfl⟩
  have hother : ∀ j, j ≠ CountSumAt.destination e → d.work j = work j := by
    intro j hj
    obtain ⟨k, hk⟩ := CountSumAt.preimage e j hj
    have h := congrArg (fun f : Fin w → Tape => f k) hdold
    change d.work (e k.castSucc) = work (e k.castSucc) at h
    simpa only [hk] using h
  have hbits : (d.work (CountSumAt.destination e)).HasBinaryPrefix (output input) := by
    simpa [output, CountSumAt.destination] using hdcur.tapePrefix
  have hsafe : ∀ j, Parked (d.work j) := by
    intro j
    by_cases hj : j = CountSumAt.destination e
    · subst j
      exact ⟨by rw [hbits.1]; omega, (show (d.work (CountSumAt.destination e)).HasBinaryContent _ from hbits.2).cells_ne_start⟩
    · rw [hother j hj]
      exact hs j
  have hcur : Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input) emitted
      d.input d.work d.output :=
    ⟨hdcur.cells, hdcur.head, fun j => ⟨(hsafe j).read_ne_start, (hsafe j).1⟩,
      by simpa only [hdout] using hc.tapePrefix, by simpa only [hdout] using hc.zero⟩
  exact ⟨d, t, ht, hreach, hhalt, hcur, hsafe, hbits, hdcur.zero, hR work d.work hother hr⟩

def copyMachine (idx : Fin (w + 1)) : TM (w + 1) := routedMachine (BoxFieldLoad.permutation idx)

theorem copy_hoareTime (idx : Fin (w + 1)) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (copyMachine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryPrefix [] ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (fun inp work out => Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryPrefix (output input) ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (input.length + 11) := by
  simpa only [copyMachine, BoxFieldLoad.destination] using routed_hoareTime (BoxFieldLoad.permutation idx)
    before input emitted R (by simpa only [BoxFieldLoad.destination] using hR)

def machine (idx : Fin (w + 1)) : TM (w + 1) :=
  seqTM (seqTM (BinaryBufferReset.machine idx) (copyMachine idx)) (rewindWorkTM idx)

theorem exact_hoareTime (idx : Fin (w + 1)) (old before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryContent old ∧ (work idx).cells 0 = Γ.start ∧ (work idx).head ≤ old.length + 1 ∧ R work)
      (fun inp work out => Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString (output input) ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (3 * old.length + input.length + 40) := by
  have hr := BinaryBufferReset.hoareTime idx old before input emitted R hR
  have hc := copy_hoareTime idx before input emitted R hR
  have hw := BinaryPrefixRewind.hoareTime idx (output input) (before ++ IntegerMachineRun.copied input)
    (NumericCursor.integerRest input) emitted R hR
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
  exact hfull.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by have := output_length input; omega)

theorem encoded_hoareTime (idx : Fin (w + 1)) (old : List Bool) (z : ℤ) (hz : z.natAbs ≤ 5)
    (before suffix emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before (BitCodec.integerCode z ++ suffix) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryContent old ∧ (work idx).cells 0 = Γ.start ∧ (work idx).head ≤ old.length + 1 ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.integerCode z) suffix emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work idx).HasBinaryString (BitCodec.integerCode z) ∧ (work idx).cells 0 = Γ.start ∧ R work)
      (3 * old.length + (BitCodec.integerCode z ++ suffix).length + 40) := by
  simpa only [output, EquationCoefficientControl.signed_value_code z hz, NumericCursor.integer_copied_code,
    NumericCursor.integer_rest_code] using exact_hoareTime idx old before (BitCodec.integerCode z ++ suffix) emitted R hR

theorem hoareTime (B : ℕ) (hB : 2 ≤ B) (idx : Fin (w + 1)) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ idx → work' j = work j) → R work → R work') :
    (machine idx).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Reusable B (work idx) ∧ R work)
      (fun inp work out => Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ (work idx).HasBinaryString (output input) ∧ Reusable B (work idx) ∧ R work)
      (12 * B + input.length + 40) := by
  rintro inp work out ⟨hc, hs, ⟨old, hold, hcontent, hz, hhead⟩, hr⟩
  obtain ⟨d, t, ht, hd, hh, hc', hs', hb', hz', hr'⟩ :=
    exact_hoareTime idx old before input emitted R hR inp work out ⟨hc, hs, hcontent, hz, hhead, hr⟩
  have hlen : (output input).length ≤ 4 * B := by have := output_length input; omega
  have hreusable : Reusable B (d.work idx) :=
    ⟨output input, hlen, hb'.2, hz', by rw [hb'.1]; omega⟩
  exact ⟨d, t, by omega, hd, hh, hc', hs', hb', hreusable, hr'⟩

end JointThermoComplexity.Complexity.EquationCoefficientLoad

#print axioms JointThermoComplexity.Complexity.EquationCoefficientLoad.output_length
#print axioms JointThermoComplexity.Complexity.EquationCoefficientLoad.exact_hoareTime
#print axioms JointThermoComplexity.Complexity.EquationCoefficientLoad.encoded_hoareTime
#print axioms JointThermoComplexity.Complexity.EquationCoefficientLoad.hoareTime
