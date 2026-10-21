module
public import proofs.JointThermoComplexity.Complexity.BoxContinuation
public import proofs.JointThermoComplexity.Complexity.ActivityFormulaEntry

set_option autoImplicit false
@[expose] public section

/-! Guard complete box emission by the retained original verdict; malformed inputs retain their complete false sentence. -/

namespace JointThermoComplexity.Complexity.BoxContinuationBranch
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def word (input : List Bool) : List Bool := match NetworkCodec.decode input with
  | none => []
  | some Q => BoxContinuation.word Q

def before (input : List Bool) : List Bool := match NetworkCodec.decode input with
  | none => []
  | some _ => input

def remaining (input : List Bool) : List Bool := match NetworkCodec.decode input with
  | none => input
  | some _ => []

def Advanced (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) : Prop := match NetworkCodec.decode input with
  | none => (∀ j, Parked (work j)) ∧ CurrentPins.Kept m input work
  | some Q => BoxState.Ready m input.length Q.speciesCount
      (fun work => CurrentPins.Kept m input work ∧ BoxRegisters.State m input work) work

def machine (m : ℕ) : TM (m + 15) :=
  FlagBranch.machine (RoutedNetworkParser.master (m + 9)) (BoxContinuation.machine m) (emitBitsTM [])

theorem hoareTime (m : ℕ) (input emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) emitted inp work out ∧
        ActivityContinuationBranch.Advanced m input work)
      (fun inp work out => Cursor (before input) (remaining input) (emitted ++ word input) inp work out ∧ Advanced m input work)
      (BoxContinuation.timeBound input.length + 2) := by
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
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 9)) (BoxContinuation.machine m) (emitBitsTM [])
      [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hp⟩
    have hp' : P work := by simpa only [ActivityContinuationBranch.Advanced, hd] using hp
    have hflag : (work (RoutedNetworkParser.master (m + 9))).read = Γ.zero := by
      rw [CurrentPins.flag m input work hp'.2, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hs, hk⟩ := hb inp work out
      ⟨⟨by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [before, remaining, word, hd, List.append_nil] using hdc,
      by simpa only [Advanced, hd] using And.intro hs hk⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    let P : (Fin (m + 15) → Tape) → Prop := fun work =>
      CurrentReady.Ready m input.length (NetworkMembership.arity Q.network) Q.speciesCount Q.speciesCount
        (CurrentResources.State m input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m))
    have hbefore : (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) ++ NetworkTallyData.tail Q = input := by
      simpa only [List.append_assoc] using (NetworkCircuitBody.input_split input Q hd).symm
    have hy := BoxContinuation.hoareTime m input Q hd (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) emitted
    have hy' : (BoxContinuation.machine m).HoareTime
        (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
          emitted inp work out ∧ P work)
        (fun inp work out => Cursor input [] (emitted ++ word input) inp work out ∧ Advanced m input work)
        (BoxContinuation.timeBound input.length) := hy.consequence
      (fun _ _ _ ⟨hc, hp, _⟩ => ⟨hc, hp⟩) (by
        rintro inp work out ⟨hc, hr⟩
        exact ⟨by simpa only [hbefore, word, hd] using hc, by simpa only [Advanced, hd] using hr⟩) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 9)) (BoxContinuation.machine m) (emitBitsTM [])
      (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q) emitted
      input [] (emitted ++ word input) P (Advanced m input) (BoxContinuation.timeBound input.length) hy'
    rintro inp work out ⟨hc, hp⟩
    have hp' : P work := by simpa only [ActivityContinuationBranch.Advanced, hd] using hp
    have hk : CurrentPins.Kept m input work := by
      rcases hp'.1 with ⟨_, _, _, _, _, _, hk, _⟩
      exact hk
    have hflag : (work (RoutedNetworkParser.master (m + 9))).read = Γ.one := by
      rw [CurrentPins.flag m input work hk, ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hdr⟩ := hb inp work out
      ⟨⟨by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh, by simpa only [before, remaining, hd] using hdc, hdr⟩

end JointThermoComplexity.Complexity.BoxContinuationBranch

#print axioms JointThermoComplexity.Complexity.BoxContinuationBranch.hoareTime
