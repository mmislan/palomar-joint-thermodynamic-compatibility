module
public import proofs.JointThermoComplexity.Complexity.CurrentSeed
public import proofs.JointThermoComplexity.Complexity.CurrentRescan

set_option autoImplicit false
@[expose] public section

/-! The actual post-circuit continuation initializes both cursors and emits the complete following current formula. -/

namespace JointThermoComplexity.Complexity.CurrentContinuation
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CircuitSerialization

def machine (m : ℕ) : TM (m + 15) := seqTM (CurrentStart.machine m) (CurrentRescan.machine m)

def timeBound (L : ℕ) : ℕ := CurrentRescan.timeBound L + 18 * L + 32

theorem timeBound_eq (L : ℕ) : timeBound L = 66 * L ^ 3 + 164 * L ^ 2 + 143 * L + 52 := by
  unfold timeBound CurrentRescan.timeBound CurrentDenseBuild.timeBound
  ring1

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
        emitted inp work out ∧ NetworkEmitReady.Ready m input.length (Q.speciesCount + Q.reactionCount)
          (NetworkMembership.gates Q.network) Q.speciesCount (NetworkPins.Kept m input) work)
      (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
        (emitted ++ (conjunctionTag ++ (NetworkMembership.equationsFormula Q.network).code)) inp work out ∧
        CurrentReady.Ready m input.length (NetworkMembership.arity Q.network) (Q.speciesCount + Q.reactionCount)
          Q.speciesCount (CurrentResources.State m input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m)))
      (timeBound input.length) := by
  have hs := CurrentSeed.hoareTime m input Q hd (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q)
    (NetworkTallyData.tail Q) emitted
  have hr := CurrentRescan.hoareTime m input Q hd emitted
  have hseq := seqTM_hoareTime (CurrentStart.machine m) (CurrentRescan.machine m) hs (by
    rintro inp work out ⟨hc, hready, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hready, hf⟩) hr
  exact hseq.consequence (fun _ _ _ hp => hp) (fun _ _ _ hp => hp) (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.CurrentContinuation

#print axioms JointThermoComplexity.Complexity.CurrentContinuation.timeBound_eq
#print axioms JointThermoComplexity.Complexity.CurrentContinuation.hoareTime
