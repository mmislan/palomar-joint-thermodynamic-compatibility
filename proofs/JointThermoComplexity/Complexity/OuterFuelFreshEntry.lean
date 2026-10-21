module
public import proofs.JointThermoComplexity.Complexity.OuterFuelInitialization

set_option autoImplicit false
@[expose] public section

/-! Fresh total input retains the exact formula prefix and initializes separate outer-loop counts on valid inputs. -/

namespace JointThermoComplexity.Complexity.OuterFuelFreshEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt OuterFuelPorts

def Advanced (m : ℕ) (input : List Bool) (work : Fin (m + 22) → Tape) : Prop := match NetworkCodec.decode input with
  | none => (∀ j, Parked (work j)) ∧ CurrentPins.Kept (m + 7) input work ∧ ProductionBank.State (m + 2) work
  | some Q => MotifPreparedMasks.Ready (m + 7) input Q work ∧ ProductionBank.State (m + 2) work ∧
      IsReg Q.speciesCount (work (destination m 0)) ∧ IsReg Q.coreCount (work (destination m 1))

def branch (m : ℕ) : TM (m + 22) :=
  FlagBranch.machine (RoutedNetworkParser.master (m + 16)) (OuterFuelInitialization.machine m) (emitBitsTM [])

theorem branch_hoareTime (m : ℕ) (input emitted : List Bool) :
    (branch m).HoareTime
      (fun inp work out => Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) emitted inp work out ∧
        MotifForwardBranch.Advanced (m + 7) input work ∧ OuterFuelBank.State m work)
      (fun inp work out => Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) emitted inp work out ∧ Advanced m input work)
      (OuterFuelInitialization.timeBound input.length + 2) := by
  cases hd : NetworkCodec.decode input with
  | none =>
    have ha : NetworkInputControl.accepted input = false := by
      cases he : NetworkInputControl.accepted input with
      | false => rfl
      | true =>
        obtain ⟨Q, hQ⟩ := (NetworkInputControl.status_iff_decode input).mp he
        rw [hd] at hQ
        cases hQ
    let P : (Fin (m + 22) → Tape) → Prop := fun work =>
      (∀ j, Parked (work j)) ∧ CurrentPins.Kept (m + 7) input work ∧ OuterFuelBank.State m work
    have hn := FixedOutput.hoareTime [] [] input emitted
      (fun work => CurrentPins.Kept (m + 7) input work ∧ OuterFuelBank.State m work)
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 16)) (OuterFuelInitialization.machine m) (emitBitsTM [])
      [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by
      simpa only [P, MotifForwardBranch.Advanced, BoxContinuationBranch.Advanced, hd, and_assoc] using And.intro hp hbank
    have hflag : (work (RoutedNetworkParser.master (m + 16))).read = Γ.zero := by
      rw [CurrentPins.flag (m + 7) input work hp'.2.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hs, hk, hb⟩ := hb inp work out
      ⟨⟨by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by unfold OuterFuelInitialization.timeBound; omega, hr, hh,
      by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd, List.append_nil] using hdc,
      by simpa only [Advanced, hd] using And.intro hs (And.intro hk (OuterFuelBank.primary m d.work hb))⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    let P : (Fin (m + 22) → Tape) → Prop := fun work => MotifPreparedMasks.Ready (m + 7) input Q work ∧ OuterFuelBank.State m work
    have hy := OuterFuelInitialization.hoareTime m input Q hd (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 16)) (OuterFuelInitialization.machine m) (emitBitsTM [])
      (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted
      P (Advanced m input) (OuterFuelInitialization.timeBound input.length) (by simpa only [Advanced, hd] using hy)
    rintro inp work out ⟨hc, hp, hbank⟩
    have hp' : P work := by simpa only [P, MotifForwardBranch.Advanced, hd] using And.intro hp hbank
    have hflag : (work (RoutedNetworkParser.master (m + 16))).read = Γ.one := by
      rw [CurrentPins.flag (m + 7) input work hp'.1.2.2.2.2.1.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hdc, hdr⟩

def machine (m : ℕ) : TM (m + 22) := seqTM (MotifForwardEntry.machine (m + 7)) (branch m)

def timeBound (L : ℕ) : ℕ := MotifForwardEntry.timeBound L + OuterFuelInitialization.timeBound L + 3

theorem timeBound_eq (L : ℕ) :
    timeBound L = 384 * L ^ 5 + 1104 * L ^ 4 + 1746 * L ^ 3 + 1784 * L ^ 2 + 1134 * L + 313 := by
  rw [timeBound, MotifForwardEntry.timeBound_eq]
  unfold OuterFuelInitialization.timeBound
  ring1

theorem run (m : ℕ) (input : List Bool) :
    ∃ d t, t ≤ timeBound input.length ∧ (machine m).reachesIn t ((machine m).initCfg input) d ∧
      (machine m).halted d ∧ Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input)
        (BoxFormulaEntry.code input) d.input d.work d.output ∧ Advanced m input d.work := by
  obtain ⟨c, tc, htc, hcreach, hchalt, hc, hregs, hbank⟩ := OuterMotifForwardEntryBank.run m input
  obtain ⟨d, td, htd, hdreach, hdhalt, hdcur, hdregs⟩ :=
    branch_hoareTime m input (BoxFormulaEntry.code input) c.input c.work c.output ⟨hc, hregs, hbank⟩
  obtain ⟨hi, hw, hout⟩ := hc.phase
  have hr : (branch m).reachesIn td
      ⟨(branch m).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ d := by
    rw [hi, hw, hout]
    exact hdreach
  have hreach := seqTM_reachesIn_of_reachesIn (MotifForwardEntry.machine (m + 7)) (branch m) hcreach hchalt hr
  have hstart : phase1Wrap (MotifForwardEntry.machine (m + 7)) (branch m)
      ((MotifForwardEntry.machine (m + 7)).initCfg input) = (machine m).initCfg input := rfl
  rw [hstart] at hreach
  exact ⟨phase2Wrap (MotifForwardEntry.machine (m + 7)) (branch m) d, tc + 1 + td,
    by unfold timeBound; omega, hreach, (phase2Wrap_halted_iff _ _ d).mpr hdhalt, hdcur, hdregs⟩

end JointThermoComplexity.Complexity.OuterFuelFreshEntry

#print axioms JointThermoComplexity.Complexity.OuterFuelFreshEntry.branch_hoareTime
#print axioms JointThermoComplexity.Complexity.OuterFuelFreshEntry.timeBound_eq
#print axioms JointThermoComplexity.Complexity.OuterFuelFreshEntry.run
