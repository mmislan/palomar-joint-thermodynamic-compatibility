module
public import proofs.JointThermoComplexity.Complexity.MotifAccess
public import proofs.JointThermoComplexity.Complexity.BoxFormulaEntry

set_option autoImplicit false
@[expose] public section

/-! Reposition valid inputs at their first motif, retaining the complete malformed-input false branch. -/

namespace JointThermoComplexity.Complexity.MotifAccessBranch
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def before (input : List Bool) : List Bool := match NetworkCodec.decode input with
  | none => []
  | some Q => MotifAccess.before Q

def remaining (input : List Bool) : List Bool := match NetworkCodec.decode input with
  | none => input
  | some Q => NetworkTallyData.tail Q

def machine (m : ℕ) : TM (m + 15) :=
  FlagBranch.machine (RoutedNetworkParser.master (m + 9)) (MotifAccess.machine m) (emitBitsTM [])

theorem hoareTime (m : ℕ) (input emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor (BoxContinuationBranch.before input) (BoxContinuationBranch.remaining input) emitted inp work out ∧
        BoxContinuationBranch.Advanced m input work)
      (fun inp work out => Cursor (before input) (remaining input) emitted inp work out ∧ BoxContinuationBranch.Advanced m input work)
      (MotifAccess.timeBound input.length + 2) := by
  cases hd : NetworkCodec.decode input with
  | none =>
    have ha : NetworkInputControl.accepted input = false := by
      cases he : NetworkInputControl.accepted input with
      | false => rfl
      | true =>
        obtain ⟨Q, hQ⟩ := (NetworkInputControl.status_iff_decode input).mp he
        rw [hd] at hQ
        cases hQ
    let P : (Fin (m + 15) → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ CurrentPins.Kept m input work
    have hn := FixedOutput.hoareTime [] [] input emitted (CurrentPins.Kept m input)
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 9)) (MotifAccess.machine m) (emitBitsTM [])
      [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hp⟩
    have hp' : P work := by simpa only [BoxContinuationBranch.Advanced, hd] using hp
    have hflag : (work (RoutedNetworkParser.master (m + 9))).read = Γ.zero := by
      rw [CurrentPins.flag m input work hp'.2, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [BoxContinuationBranch.before, BoxContinuationBranch.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh, by simpa only [before, remaining, hd, List.append_nil] using hdc,
      by simpa only [BoxContinuationBranch.Advanced, hd] using hdr⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    let P := BoxContinuationBranch.Advanced m input
    have hy := MotifAccess.hoareTime m input Q hd emitted (fun work _ => P work)
    have hy' : (MotifAccess.machine m).HoareTime
        (fun inp work out => Cursor input [] emitted inp work out ∧ P work)
        (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧ P work)
        (MotifAccess.timeBound input.length) := hy.consequence (by
      rintro inp work out ⟨hc, hp⟩
      have hready : BoxState.Ready m input.length Q.speciesCount
          (fun work => CurrentPins.Kept m input work ∧ BoxRegisters.State m input work) work := by
        simpa only [P, BoxContinuationBranch.Advanced, hd] using hp
      exact ⟨hc, hready.1, hready.2.2.2.2.1, hp⟩)
      (fun _ _ _ ⟨hc, _, _, hp⟩ => ⟨hc, hp⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 9)) (MotifAccess.machine m) (emitBitsTM [])
      input [] emitted (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted P P
      (MotifAccess.timeBound input.length) hy'
    rintro inp work out ⟨hc, hp⟩
    have hready : BoxState.Ready m input.length Q.speciesCount
        (fun work => CurrentPins.Kept m input work ∧ BoxRegisters.State m input work) work := by
      simpa only [BoxContinuationBranch.Advanced, hd] using hp
    have hflag : (work (RoutedNetworkParser.master (m + 9))).read = Γ.one := by
      rw [CurrentPins.flag m input work hready.2.2.2.2.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [BoxContinuationBranch.before, BoxContinuationBranch.remaining, hd] using hc, hp⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh, by simpa only [before, remaining, hd] using hdc, hdr⟩

end JointThermoComplexity.Complexity.MotifAccessBranch

#print axioms JointThermoComplexity.Complexity.MotifAccessBranch.hoareTime
