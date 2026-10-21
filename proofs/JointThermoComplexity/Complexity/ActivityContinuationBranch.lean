module
public import proofs.JointThermoComplexity.Complexity.ActivityContinuation
public import proofs.JointThermoComplexity.Complexity.CurrentFormulaEntry

set_option autoImplicit false
@[expose] public section

/-! The retained master verdict guards positivity emission and preserves the complete malformed-input result. -/

namespace JointThermoComplexity.Complexity.ActivityContinuationBranch
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def word (input : List Bool) : List Bool := match NetworkCodec.decode input with
  | none => []
  | some Q => ActivityContinuation.word Q

def Advanced (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) : Prop :=
  match NetworkCodec.decode input with
  | none => (∀ j, Parked (work j)) ∧ CurrentPins.Kept m input work
  | some Q => CurrentReady.Ready m input.length (NetworkMembership.arity Q.network) Q.speciesCount
      Q.speciesCount (CurrentResources.State m input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m))

def machine (m : ℕ) : TM (m + 15) :=
  FlagBranch.machine (RoutedNetworkParser.master (m + 9)) (ActivityStart.machine m) (emitBitsTM [])

theorem hoareTime (m : ℕ) (input emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) emitted inp work out ∧
        CurrentContinuationBranch.Advanced m input work)
      (fun inp work out => Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input)
        (emitted ++ word input) inp work out ∧ Advanced m input work) (ActivityStart.timeBound input.length + 2) := by
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
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 9)) (ActivityStart.machine m) (emitBitsTM [])
      [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hp⟩
    have hp' : P work := by simpa only [CurrentContinuationBranch.Advanced, hd] using hp
    have hflag : (work (RoutedNetworkParser.master (m + 9))).read = Γ.zero := by
      rw [CurrentPins.flag m input work hp'.2, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hs, hk⟩ := hb inp work out
      ⟨⟨by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, word, hd] using hdc,
      by simpa only [Advanced, hd] using And.intro hs hk⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    let P : (Fin (m + 15) → Tape) → Prop := fun work => CurrentReady.Ready m input.length
      (NetworkMembership.arity Q.network) (Q.speciesCount + Q.reactionCount) Q.speciesCount (CurrentResources.State m input) work ∧
      IsReg Q.reactionCount (work (ReactionFuel.slot m))
    have hy := ActivityContinuation.hoareTime m input Q hd (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) emitted
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 9)) (ActivityStart.machine m) (emitBitsTM [])
      (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) emitted
      (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) (emitted ++ word input)
      P (Advanced m input) (ActivityStart.timeBound input.length) (by simpa only [word, Advanced, hd] using hy)
    rintro inp work out ⟨hc, hp⟩
    have hp' : P work := by simpa only [CurrentContinuationBranch.Advanced, hd] using hp
    have hres : CurrentResources.State m input work := hp'.1.2.2.2.2.2.2
    have hflag : (work (RoutedNetworkParser.master (m + 9))).read = Γ.one := by
      rw [CurrentPins.flag m input work hres.1, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hpost⟩ := hb inp work out ⟨⟨hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh, hdc, hpost⟩

end JointThermoComplexity.Complexity.ActivityContinuationBranch

#print axioms JointThermoComplexity.Complexity.ActivityContinuationBranch.hoareTime
