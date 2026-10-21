module
public import proofs.JointThermoComplexity.Complexity.CurrentSeedBank
public import proofs.JointThermoComplexity.Complexity.CurrentRescanBank
public import proofs.JointThermoComplexity.Complexity.CurrentContinuation

set_option autoImplicit false
@[expose] public section

/-! The existing complete current continuation preserves the reserved production bank with unchanged cost. -/

namespace JointThermoComplexity.Complexity.CurrentContinuationBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CircuitSerialization

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) :
    (CurrentContinuation.machine (m + 5)).HoareTime
      (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
        emitted inp work out ∧ NetworkEmitReady.Ready (m + 5) input.length (Q.speciesCount + Q.reactionCount)
          (NetworkMembership.gates Q.network) Q.speciesCount (NetworkPins.Kept (m + 5) input) work ∧ ProductionBank.State m work)
      (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
        (emitted ++ (conjunctionTag ++ (NetworkMembership.equationsFormula Q.network).code)) inp work out ∧
        CurrentReady.Ready (m + 5) input.length (NetworkMembership.arity Q.network) (Q.speciesCount + Q.reactionCount)
          Q.speciesCount (CurrentResources.State (m + 5) input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot (m + 5))) ∧ ProductionBank.State m work)
      (CurrentContinuation.timeBound input.length) := by
  have hs := CurrentSeedBank.hoareTime m input Q hd (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q)
    (NetworkTallyData.tail Q) emitted
  have hr := CurrentRescanBank.hoareTime m input Q hd emitted
  have hfull := seqTM_hoareTime (CurrentStart.machine (m + 5)) (CurrentRescan.machine (m + 5)) hs (by
    rintro inp work out ⟨hc, hp, hf, hb⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp, hf, hb⟩) hr
  exact hfull.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold CurrentContinuation.timeBound; omega)

end JointThermoComplexity.Complexity.CurrentContinuationBank

#print axioms JointThermoComplexity.Complexity.CurrentContinuationBank.hoareTime
