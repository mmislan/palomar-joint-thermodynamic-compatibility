module
public import proofs.JointThermoComplexity.Complexity.MotifForwardPreload
public import proofs.JointThermoComplexity.Complexity.MotifPreparedMasks
public import proofs.JointThermoComplexity.Complexity.MotifAccessEntry

set_option autoImplicit false
@[expose] public section

/-! Guard common-orientation preparation by the original validated verdict. -/

namespace JointThermoComplexity.Complexity.MotifForwardBranch
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def Advanced (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) : Prop := match NetworkCodec.decode input with
  | none => BoxContinuationBranch.Advanced m input work
  | some Q => MotifPreparedMasks.Ready m input Q work

def machine (m : ℕ) : TM (m + 15) :=
  FlagBranch.machine (RoutedNetworkParser.master (m + 9)) (MotifForwardPreload.machine m) (emitBitsTM [])

theorem hoareTime (m : ℕ) (input emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) emitted inp work out ∧
        BoxContinuationBranch.Advanced m input work)
      (fun inp work out => Cursor (MotifAccessBranch.before input) (MotifAccessBranch.remaining input) emitted inp work out ∧
        Advanced m input work) (MotifForwardPreload.timeBound input.length + 2) := by
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
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 9)) (MotifForwardPreload.machine m) (emitBitsTM [])
      [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hp⟩
    have hp' : P work := by simpa only [BoxContinuationBranch.Advanced, hd] using hp
    have hflag : (work (RoutedNetworkParser.master (m + 9))).read = Γ.zero := by
      rw [CurrentPins.flag m input work hp'.2, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd, List.append_nil] using hdc,
      by simpa only [Advanced, BoxContinuationBranch.Advanced, hd] using hdr⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    let P := BoxState.Ready m input.length Q.speciesCount (MotifBufferMeta.State m input)
    have hy := MotifForwardPreload.hoareTime m Q.speciesCount input Q hd emitted (MotifBufferMeta.State m input)
      (MotifBufferMeta.frame m input 2) (fun _ h => h.1)
    have hy' : (MotifForwardPreload.machine m).HoareTime
        (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧ P work)
        (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧ Advanced m input work)
        (MotifForwardPreload.timeBound input.length) := hy.consequence (fun _ _ _ h => h) (by
      rintro inp work out ⟨hc, hp, hf⟩
      exact ⟨hc, by simpa only [Advanced, hd] using (MotifPreparedMasks.ready_iff m input Q work).mpr ⟨hp, hf⟩⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 9)) (MotifForwardPreload.machine m) (emitBitsTM [])
      (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted P
      (Advanced m input) (MotifForwardPreload.timeBound input.length) hy'
    rintro inp work out ⟨hc, hp⟩
    have hp' : P work := by simpa only [P, BoxState.Ready, MotifBufferMeta.State, BoxContinuationBranch.Advanced, hd] using hp
    have hflag : (work (RoutedNetworkParser.master (m + 9))).read = Γ.one := by
      rw [CurrentPins.flag m input work hp'.2.2.2.2.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [MotifAccessBranch.before, MotifAccessBranch.remaining, hd] using hdc, hdr⟩

end JointThermoComplexity.Complexity.MotifForwardBranch

#print axioms JointThermoComplexity.Complexity.MotifForwardBranch.hoareTime
