module
public import proofs.JointThermoComplexity.Complexity.CurrentDecodedBuild
public import proofs.JointThermoComplexity.Complexity.CurrentPins
public import proofs.JointThermoComplexity.Complexity.CurrentResources
public import proofs.JointThermoComplexity.Complexity.NetworkCircuitBody

set_option autoImplicit false
@[expose] public section

/-! Restart the original input, skip its headers and append the following conjunction plus the exact current formula. -/

namespace JointThermoComplexity.Complexity.CurrentRescan
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CurrentReady CircuitSerialization

def machine (m : ℕ) : TM (m + 15) := seqTM rewindInputTM
  (seqTM DimensionSkip.machine (seqTM (emitBitsTM conjunctionTag) (CurrentDenseBuild.machine m)))

def timeBound (L : ℕ) : ℕ := CurrentDenseBuild.timeBound L + 2 * L + 14

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
        emitted inp work out ∧ Ready m input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount Q.speciesCount
          (CurrentResources.State m input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m)))
      (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
        (emitted ++ (conjunctionTag ++ (NetworkMembership.equationsFormula Q.network).code)) inp work out ∧
        Ready m input.length (NetworkMembership.arity Q.network) (Q.speciesCount + Q.reactionCount) Q.speciesCount
          (CurrentResources.State m input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot m)))
      (timeBound input.length) := by
  let S : (Fin (m + 15) → Tape) → Prop := fun work =>
    Ready m input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount Q.speciesCount (CurrentResources.State m input) work ∧
      IsReg Q.reactionCount (work (ReactionFuel.slot m))
  have hr := InputRewind.hoareTime (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q) emitted S
  have hs := DimensionSkip.hoareTime Q.speciesCount Q.reactionCount Q.coreCount []
    (NetworkCircuitBody.table Q ++ NetworkTallyData.tail Q) emitted S
  have ht := FixedOutput.hoareTime conjunctionTag (NetworkTallyData.headers Q)
    (NetworkCircuitBody.table Q ++ NetworkTallyData.tail Q) emitted S
  have hb := CurrentDecodedBuild.hoareTime m input Q hd (NetworkTallyData.headers Q) (NetworkTallyData.tail Q)
    (emitted ++ conjunctionTag) (CurrentResources.State m input) (CurrentResources.frame m input)
  have htail := seqTM_hoareTime (emitBitsTM conjunctionTag) (CurrentDenseBuild.machine m) ht (by
    rintro inp work out ⟨hc, _, hready, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hready, hf⟩) hb
  have hbody := seqTM_hoareTime DimensionSkip.machine
    (seqTM (emitBitsTM conjunctionTag) (CurrentDenseBuild.machine m)) hs (by
      rintro inp work out ⟨hc, hsafe, hready, hf⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨by simpa only [List.nil_append, NetworkTallyData.headers] using hc, hsafe, hready, hf⟩) htail
  have hfull := seqTM_hoareTime rewindInputTM
    (seqTM DimensionSkip.machine (seqTM (emitBitsTM conjunctionTag) (CurrentDenseBuild.machine m))) hr (by
      rintro inp work out ⟨hc, hready, hf⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨by simpa only [NetworkTallyData.headers, List.append_assoc] using hc, hready.1, hready, hf⟩) hbody
  exact hfull.consequence (fun _ _ _ hp => hp) (by
    rintro inp work out ⟨hc, hready, hf⟩
    exact ⟨by simpa only [NetworkCircuitBody.table, List.append_assoc] using hc, hready, hf⟩) (by
      have hdim := NetworkCodec.decoded_dimensions_le_length hd
      have hsplit := NetworkCircuitBody.input_split input Q hd
      have hp : (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q).length ≤ input.length := by
        have hh := congrArg List.length hsplit
        simp only [List.length_append] at hh ⊢
        omega
      unfold timeBound
      simp only [conjunctionTag, List.length_cons, List.length_nil]
      omega)

end JointThermoComplexity.Complexity.CurrentRescan

#print axioms JointThermoComplexity.Complexity.CurrentRescan.hoareTime
