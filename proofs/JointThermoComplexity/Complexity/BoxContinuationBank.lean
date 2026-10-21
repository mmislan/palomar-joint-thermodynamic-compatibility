module
public import proofs.JointThermoComplexity.Complexity.BoxContinuation
public import proofs.JointThermoComplexity.Complexity.ActivityBoxBankFrame

set_option autoImplicit false
@[expose] public section

/-! Read-only box access and complete rational-box output preserve the production bank. -/

namespace JointThermoComplexity.Complexity.BoxContinuationBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before emitted : List Bool) :
    (BoxContinuation.machine (m + 5)).HoareTime
      (fun inp work out => Cursor before (NetworkTallyData.tail Q) emitted inp work out ∧
        CurrentReady.Ready (m + 5) input.length (NetworkMembership.arity Q.network) Q.speciesCount Q.speciesCount
          (CurrentResources.State (m + 5) input) work ∧ ProductionBank.State m work)
      (fun inp work out => Cursor (before ++ NetworkTallyData.tail Q) [] (emitted ++ BoxContinuation.word Q) inp work out ∧
        BoxState.Ready (m + 5) input.length Q.speciesCount
          (fun work => CurrentPins.Kept (m + 5) input work ∧ BoxRegisters.State (m + 5) input work) work ∧ ProductionBank.State m work)
      (BoxContinuation.timeBound input.length) := by
  let C : (Fin (m + 20) → Tape) → Prop := fun work => CurrentReady.Ready (m + 5) input.length
    (NetworkMembership.arity Q.network) Q.speciesCount Q.speciesCount (CurrentResources.State (m + 5) input) work ∧ ProductionBank.State m work
  let R : (Fin (m + 20) → Tape) → Prop := fun work => BoxRegisters.State (m + 5) input work ∧ ProductionBank.State m work
  have hR : ∀ work work', BoxState.Unchanged (m + 5) work work' → R work → R work' := by
    rintro work work' hw ⟨hr, hb⟩
    exact ⟨BoxRegisters.frame (m + 5) input work work' hw hr, ActivityBoxBankFrame.box_frame m work work' hw hb⟩
  have ha := BoxAccess.hoareTime (m + 5) input Q hd before emitted (fun work _ => C work)
  have hs := BoxStart.hoareTime (m + 5) Q.speciesCount input Q hd (BoxDecodedBounds.species input Q hd)
    (BoxContinuation.tableBefore Q before) [] emitted R hR
  have hseq := seqTM_hoareTime (BoxAccess.machine (m + 5)) (BoxStart.machine (m + 5)) ha (by
    rintro inp work out ⟨hc, _, hr, hb⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    have hseed := BoxSeed.of_current (m + 5) input Q hd work hr
    exact ⟨by simpa only [BoxContinuation.tableBefore, List.append_nil] using hc,
      by simpa only [BoxState.Ready, R, and_assoc] using And.intro hseed hb⟩) hs
  exact hseq.consequence (by
    rintro inp work out ⟨hc, hr, hb⟩
    have hk : CurrentPins.Kept (m + 5) input work := by
      rcases hr with ⟨_, _, _, _, _, _, hk, _⟩
      exact hk
    exact ⟨hc, hk, hr, hb⟩) (by
      rintro inp work out ⟨hc, hr⟩
      have hpost : BoxState.Ready (m + 5) input.length Q.speciesCount
          (fun work => CurrentPins.Kept (m + 5) input work ∧ BoxRegisters.State (m + 5) input work) work ∧ ProductionBank.State m work := by
        simpa only [BoxState.Ready, R, and_assoc] using hr
      exact ⟨by simpa only [BoxContinuation.word, BoxContinuation.tableBefore, BoxTraversalData.tail_split, List.append_assoc] using hc, hpost⟩)
    (by unfold BoxContinuation.timeBound; omega)

end JointThermoComplexity.Complexity.BoxContinuationBank

#print axioms JointThermoComplexity.Complexity.BoxContinuationBank.hoareTime
