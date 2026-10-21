module
public import proofs.JointThermoComplexity.Complexity.MotifFormulaSuffix

set_option autoImplicit false
@[expose] public section

/-! The retained validation flag appends the complete motif block only on valid input and preserves malformed falsity. -/

namespace JointThermoComplexity.Complexity.MotifContinuationBranch
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def machine (m : ℕ) : TM (m + 22) :=
  FlagBranch.machine (RoutedNetworkParser.master (m + 16)) (MotifCoreBlock.machine m) (emitBitsTM [])

def Final (m : ℕ) (input : List Bool) (work : Fin (m + 22) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ CurrentPins.Kept (m + 7) input work

theorem hoareTime (m : ℕ) (input emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) emitted inp work out ∧
        OuterFuelFreshEntry.Advanced m input work)
      (fun inp work out => Cursor [] input (emitted ++ MotifFormulaSuffix.word input) inp work out ∧ Final m input work)
      (MotifCoreBlock.timeBound input.length + 2) := by
  cases hd : NetworkCodec.decode input with
  | none =>
    have ha : NetworkInputControl.accepted input = false := by
      cases he : NetworkInputControl.accepted input with
      | false => rfl
      | true =>
        obtain ⟨Q, hQ⟩ := (NetworkInputControl.status_iff_decode input).mp he
        rw [hd] at hQ
        cases hQ
    have hn := FixedOutput.hoareTime [] [] input emitted (CurrentPins.Kept (m + 7) input)
    have hn' := hn.mono_bound (b' := MotifCoreBlock.timeBound input.length) (Nat.zero_le _)
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 16)) (MotifCoreBlock.machine m) (emitBitsTM [])
      [] input emitted [] input (emitted ++ []) (Final m input) (Final m input) (MotifCoreBlock.timeBound input.length) hn'
    rintro inp work out ⟨hc, hp⟩
    have hp' : Final m input work := by
      have h : (∀ j, Parked (work j)) ∧ CurrentPins.Kept (m + 7) input work ∧ ProductionBank.State (m + 2) work := by
        simpa only [OuterFuelFreshEntry.Advanced, hd] using hp
      exact ⟨h.1, h.2.1⟩
    have hflag : (work (RoutedNetworkParser.master (m + 16))).read = Γ.zero := by
      rw [CurrentPins.flag (m + 7) input work hp'.2, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, ht, hr, hh, by simpa only [MotifFormulaSuffix.word, hd] using hdc, hdr⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    have hsplit : MotifAccess.before Q ++ NetworkTallyData.tail Q = input := by
      simpa only [MotifPrefixData.first_before, MotifPrefixData.first_remaining] using MotifPrefixData.input_split input Q hd 0
    have hy := MotifCoreBlock.hoareTime m input Q hd (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted hsplit
      (fun _ => True) (fun _ _ _ _ => True.intro)
    have hy' : (MotifCoreBlock.machine m).HoareTime
        (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧
          OuterFuelFreshEntry.Advanced m input work)
        (fun inp work out => Cursor [] input (emitted ++ (MotifCoreDenseCode.formula Q).code) inp work out ∧ Final m input work)
        (MotifCoreBlock.timeBound input.length) :=
      hy.consequence (by
        rintro inp work out ⟨hc, hp⟩
        obtain ⟨hs, hspecies, hcore⟩ := MotifCoreState.of_fresh m input Q hd (fun _ => True) work hp True.intro
        exact ⟨hc, hs, hspecies, hcore⟩) (by
          rintro inp work out ⟨hc, hp, _, _⟩
          exact ⟨hc, hp.1.1, hp.1.2.2.2.2.1.1⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 16)) (MotifCoreBlock.machine m) (emitBitsTM [])
      (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted [] input (emitted ++ (MotifCoreDenseCode.formula Q).code)
      (OuterFuelFreshEntry.Advanced m input) (Final m input) (MotifCoreBlock.timeBound input.length) hy'
    rintro inp work out ⟨hc, hp⟩
    have hp' : MotifPreparedMasks.Ready (m + 7) input Q work ∧ ProductionBank.State (m + 2) work ∧
        IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) ∧ IsReg Q.coreCount (work (OuterFuelPorts.destination m 1)) := by
      simpa only [OuterFuelFreshEntry.Advanced, hd] using hp
    have hflag : (work (RoutedNetworkParser.master (m + 16))).read = Γ.one := by
      rw [CurrentPins.flag (m + 7) input work hp'.1.2.2.2.2.1.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hc, hp⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh, by simpa only [MotifFormulaSuffix.word, hd] using hdc, hdr⟩

end JointThermoComplexity.Complexity.MotifContinuationBranch

#print axioms JointThermoComplexity.Complexity.MotifContinuationBranch.hoareTime
