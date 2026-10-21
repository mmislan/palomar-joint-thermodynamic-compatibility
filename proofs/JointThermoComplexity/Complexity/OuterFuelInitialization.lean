module
public import proofs.JointThermoComplexity.Complexity.OuterFuelCopyFrame

set_option autoImplicit false
@[expose] public section

/-! Initialize copied species/core loop fuel while retaining the original counts, fresh production bank and prepared motif resources. -/

namespace JointThermoComplexity.Complexity.OuterFuelInitialization
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt OuterFuelPorts

theorem prepared_copy_hoareTime (m : ℕ) (k : Fin 2) (old value : ℕ) (input : List Bool) (Q : NetworkCodec.Input)
    (before remaining emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ destination m k → work' j = work j) → R work → R work') :
    (OuterFuelCopy.machine m k).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ MotifPreparedMasks.Ready (m + 7) input Q work ∧
        ProductionBank.State (m + 2) work ∧ IsReg old (work (destination m k)) ∧ IsReg value (work (source m k)) ∧ R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ MotifPreparedMasks.Ready (m + 7) input Q work ∧
        ProductionBank.State (m + 2) work ∧ IsReg value (work (destination m k)) ∧ R work) (2 * old + 5 * value + 15) := by
  rintro inp work out ⟨hc, hp, hb, hd, hs, hr⟩
  let P : (Fin (m + 22) → Tape) → Prop := fun work' => ∀ j, j ≠ destination m k → work' j = work j
  have hP : ∀ work' work'', (∀ j, j ≠ destination m k → work'' j = work' j) → P work' → P work'' := by
    intro work' work'' hw hp j hj
    exact (hw j hj).trans (hp j hj)
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hdsafe, hdest, _, hw⟩ :=
    OuterFuelCopy.hoareTime m k old value before remaining emitted P hP
      inp work out ⟨hc, hp.1, hd, hs, hp.2.1, fun _ _ => rfl⟩
  exact ⟨d, t, ht, hreach, hhalt, hdc,
    OuterFuelCopyFrame.prepared_replace m input Q k work d.work hw (hdsafe _) hp,
    OuterFuelCopyFrame.bank m work d.work (OuterFuelCopyFrame.of_single m k work d.work hw) hb,
    hdest, hR work d.work hw hr⟩

theorem species_hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before remaining emitted : List Bool) :
    (OuterFuelCopy.machine m 0).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ MotifPreparedMasks.Ready (m + 7) input Q work ∧
        ProductionBank.State (m + 2) work ∧ IsReg 0 (work (destination m 0)) ∧ IsReg 0 (work (destination m 1)))
      (fun inp work out => Cursor before remaining emitted inp work out ∧ MotifPreparedMasks.Ready (m + 7) input Q work ∧
        ProductionBank.State (m + 2) work ∧ IsReg Q.speciesCount (work (destination m 0)) ∧ IsReg 0 (work (destination m 1)))
      (5 * Q.speciesCount + 15) := by
  have ht := prepared_copy_hoareTime m 0 0 Q.speciesCount input Q before remaining emitted
    (fun work => IsReg 0 (work (destination m 1))) (by
      intro work work' hw hr
      rw [hw _ (destination_ne m).symm]
      exact hr)
  exact ht.consequence (by
    rintro inp work out ⟨hc, hp, hb, h0, h1⟩
    have hcounts := OuterFuelCopyFrame.counts m input Q hd work hp.2.2.2.2.1.1
    exact ⟨hc, hp, hb, h0, hcounts.1, h1⟩) (fun _ _ _ h => h) (by omega)

theorem core_hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before remaining emitted : List Bool) :
    (OuterFuelCopy.machine m 1).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ MotifPreparedMasks.Ready (m + 7) input Q work ∧
        ProductionBank.State (m + 2) work ∧ IsReg Q.speciesCount (work (destination m 0)) ∧ IsReg 0 (work (destination m 1)))
      (fun inp work out => Cursor before remaining emitted inp work out ∧ MotifPreparedMasks.Ready (m + 7) input Q work ∧
        ProductionBank.State (m + 2) work ∧ IsReg Q.speciesCount (work (destination m 0)) ∧ IsReg Q.coreCount (work (destination m 1)))
      (5 * Q.coreCount + 15) := by
  have ht := prepared_copy_hoareTime m 1 0 Q.coreCount input Q before remaining emitted
    (fun work => IsReg Q.speciesCount (work (destination m 0))) (by
      intro work work' hw hr
      rw [hw _ (destination_ne m)]
      exact hr)
  exact ht.consequence (by
    rintro inp work out ⟨hc, hp, hb, hn, h0⟩
    have hcounts := OuterFuelCopyFrame.counts m input Q hd work hp.2.2.2.2.1.1
    exact ⟨hc, hp, hb, h0, hcounts.2, hn⟩) (by
      rintro inp work out ⟨hc, hp, hb, hcore, hn⟩
      exact ⟨hc, hp, hb, hn, hcore⟩) (by omega)

def machine (m : ℕ) : TM (m + 22) := seqTM (OuterFuelCopy.machine m 0) (OuterFuelCopy.machine m 1)

def timeBound (L : ℕ) : ℕ := 10 * L + 31

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before remaining emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ MotifPreparedMasks.Ready (m + 7) input Q work ∧ OuterFuelBank.State m work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ MotifPreparedMasks.Ready (m + 7) input Q work ∧
        ProductionBank.State (m + 2) work ∧ IsReg Q.speciesCount (work (destination m 0)) ∧ IsReg Q.coreCount (work (destination m 1)))
      (timeBound input.length) := by
  have hn := species_hoareTime m input Q hd before remaining emitted
  have hc := core_hoareTime m input Q hd before remaining emitted
  have hs := seqTM_hoareTime (OuterFuelCopy.machine m 0) (OuterFuelCopy.machine m 1) hn (by
    rintro inp work out ⟨hcur, hp, hb, hn, hzero⟩
    obtain ⟨hi, hw, ho⟩ := hcur.phase
    rw [hi, hw, ho]
    exact ⟨hcur, hp, hb, hn, hzero⟩) hc
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  exact hs.consequence (by
    rintro inp work out ⟨hc, hp, hb⟩
    exact ⟨hc, hp, OuterFuelBank.primary m work hb, initial m work hb 0, initial m work hb 1⟩)
    (fun _ _ _ h => h) (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.OuterFuelInitialization

#print axioms JointThermoComplexity.Complexity.OuterFuelInitialization.prepared_copy_hoareTime
#print axioms JointThermoComplexity.Complexity.OuterFuelInitialization.hoareTime
