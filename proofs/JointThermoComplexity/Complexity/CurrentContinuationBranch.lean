module
public import proofs.JointThermoComplexity.Complexity.CurrentContinuation
public import proofs.JointThermoComplexity.Complexity.NetworkCircuitEntry

set_option autoImplicit false
@[expose] public section

/-! Guard the actual continuation by the retained original validation verdict. -/

namespace JointThermoComplexity.Complexity.CurrentContinuationBranch
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CircuitSerialization

def word (input : List Bool) : List Bool := match NetworkCodec.decode input with
  | none => []
  | some Q => conjunctionTag ++ (NetworkMembership.equationsFormula Q.network).code

def Advanced (m : ℕ) (input : List Bool) (work : Fin (m + 15) → Tape) : Prop :=
  match NetworkCodec.decode input with
  | none => (∀ j, Parked (work j)) ∧ CurrentPins.Kept m input work
  | some Q => CurrentReady.Ready m input.length (NetworkMembership.arity Q.network) (Q.speciesCount + Q.reactionCount)
      Q.speciesCount (CurrentResources.State m input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m))

def machine (m : ℕ) : TM (m + 15) :=
  FlagBranch.machine (RoutedNetworkParser.master (m + 9)) (CurrentContinuation.machine m) (emitBitsTM [])

theorem hoareTime (m : ℕ) (input emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input) emitted inp work out ∧
        NetworkCircuitEntry.Advanced m input work)
      (fun inp work out => Cursor (NetworkCircuitEntry.before input) (NetworkCircuitEntry.remaining input)
        (emitted ++ word input) inp work out ∧ Advanced m input work)
      (CurrentContinuation.timeBound input.length + 2) := by
  cases hd : NetworkCodec.decode input with
  | none =>
    have ha : NetworkInputControl.accepted input = false := by
      cases he : NetworkInputControl.accepted input with
      | false => rfl
      | true =>
        obtain ⟨Q, hQ⟩ := (NetworkInputControl.status_iff_decode input).mp he
        rw [hd] at hQ
        cases hQ
    let P : (Fin (m + 15) → Tape) → Prop := fun work => (∀ j, Parked (work j)) ∧ NetworkPins.Kept m input work
    have hn := FixedOutput.hoareTime [] [] input emitted (NetworkPins.Kept m input)
    have hb := FlagBranchRun.no_hoareTime (RoutedNetworkParser.master (m + 9)) (CurrentContinuation.machine m) (emitBitsTM [])
      [] input emitted [] input (emitted ++ []) P P 0 hn
    rintro inp work out ⟨hc, hp⟩
    have hp' : P work := by simpa only [NetworkCircuitEntry.Advanced, hd] using hp
    have hflag : (work (RoutedNetworkParser.master (m + 9))).read = Γ.zero := by
      rw [CurrentPins.flag m input work (CurrentPins.of_network m input work hp'.2), ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hs, hk⟩ := hb inp work out
      ⟨⟨by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, word, hd] using hdc,
      by simpa only [Advanced, hd] using And.intro hs (CurrentPins.of_network m input d.work hk)⟩
  | some Q =>
    have ha : NetworkInputControl.accepted input = true := (NetworkInputControl.status_iff_decode input).mpr ⟨Q, hd⟩
    let P : (Fin (m + 15) → Tape) → Prop := fun work => NetworkEmitReady.Ready m input.length
      (Q.speciesCount + Q.reactionCount) (NetworkMembership.gates Q.network) Q.speciesCount (NetworkPins.Kept m input) work ∧
      IsReg Q.reactionCount (work (ReactionFuel.slot m))
    have hy := CurrentContinuation.hoareTime m input Q hd emitted
    have hy' : (CurrentContinuation.machine m).HoareTime
        (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q) emitted inp work out ∧ P work)
        (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
          (emitted ++ word input) inp work out ∧ Advanced m input work) (CurrentContinuation.timeBound input.length) := by
      exact hy.consequence (fun _ _ _ ⟨hc, hp, _⟩ => ⟨hc, hp⟩)
        (fun _ _ _ hp => by simpa only [word, Advanced, hd] using hp) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (RoutedNetworkParser.master (m + 9)) (CurrentContinuation.machine m) (emitBitsTM [])
      (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q) emitted
      (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q) (emitted ++ word input)
      P (Advanced m input) (CurrentContinuation.timeBound input.length) hy'
    rintro inp work out ⟨hc, hp⟩
    have hp' : P work := by simpa only [NetworkCircuitEntry.Advanced, hd] using hp
    have hk : NetworkPins.Kept m input work := hp'.1.2.2.2.2.2.2.2.2
    have hflag : (work (RoutedNetworkParser.master (m + 9))).read = Γ.one := by
      rw [CurrentPins.flag m input work (CurrentPins.of_network m input work hk), ha]
      rfl
    obtain ⟨d, t, ht, hr, hh, hdc, hpost⟩ := hb inp work out
      ⟨⟨by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hc, hp'⟩, hflag⟩
    exact ⟨d, t, by omega, hr, hh,
      by simpa only [NetworkCircuitEntry.before, NetworkCircuitEntry.remaining, hd] using hdc, hpost⟩

end JointThermoComplexity.Complexity.CurrentContinuationBranch

#print axioms JointThermoComplexity.Complexity.CurrentContinuationBranch.hoareTime
