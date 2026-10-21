module
public import proofs.JointThermoComplexity.Complexity.OuterCurrentBankFrame
public import proofs.JointThermoComplexity.Complexity.CurrentRescan

set_option autoImplicit false
@[expose] public section

/-! The complete original current-equation rescan retains the blank production bank without extra transitions. -/

namespace JointThermoComplexity.Complexity.OuterCurrentRescanBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CurrentReady CircuitSerialization

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) :
    (CurrentRescan.machine (m + 7)).HoareTime
      (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
        emitted inp work out ∧ Ready (m + 7) input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount Q.speciesCount
          (CurrentResources.State (m + 7) input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot (m + 7))) ∧ OuterFuelBank.State m work)
      (fun inp work out => Cursor (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q)
        (emitted ++ (conjunctionTag ++ (NetworkMembership.equationsFormula Q.network).code)) inp work out ∧
        Ready (m + 7) input.length (NetworkMembership.arity Q.network) (Q.speciesCount + Q.reactionCount) Q.speciesCount
          (CurrentResources.State (m + 7) input) work ∧ IsReg Q.reactionCount (work (ReactionFuel.slot (m + 7))) ∧ OuterFuelBank.State m work)
      (CurrentRescan.timeBound input.length) := by
  let R : (Fin (m + 22) → Tape) → Prop := fun work => CurrentResources.State (m + 7) input work ∧ OuterFuelBank.State m work
  let S : (Fin (m + 22) → Tape) → Prop := fun work =>
    Ready (m + 7) input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount Q.speciesCount R work ∧
      IsReg Q.reactionCount (work (ReactionFuel.slot (m + 7)))
  have hr := InputRewind.hoareTime (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q) (NetworkTallyData.tail Q) emitted S
  have hs := DimensionSkip.hoareTime Q.speciesCount Q.reactionCount Q.coreCount []
    (NetworkCircuitBody.table Q ++ NetworkTallyData.tail Q) emitted S
  have ht := FixedOutput.hoareTime conjunctionTag (NetworkTallyData.headers Q)
    (NetworkCircuitBody.table Q ++ NetworkTallyData.tail Q) emitted S
  have hb := CurrentDecodedBuild.hoareTime (m + 7) input Q hd (NetworkTallyData.headers Q) (NetworkTallyData.tail Q)
    (emitted ++ conjunctionTag) R (by
      rintro work work' hw ⟨hp, hb⟩
      exact ⟨CurrentResources.frame (m + 7) input work work' hw hp, OuterCurrentBankFrame.build_frame m work work' hw hb⟩)
  have htail := seqTM_hoareTime (emitBitsTM conjunctionTag) (CurrentDenseBuild.machine (m + 7)) ht (by
    rintro inp work out ⟨hc, _, hready, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hready, hf⟩) hb
  have hbody := seqTM_hoareTime DimensionSkip.machine
    (seqTM (emitBitsTM conjunctionTag) (CurrentDenseBuild.machine (m + 7))) hs (by
      rintro inp work out ⟨hc, hsafe, hready, hf⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨by simpa only [List.nil_append, NetworkTallyData.headers] using hc, hsafe, hready, hf⟩) htail
  have hfull := seqTM_hoareTime rewindInputTM
    (seqTM DimensionSkip.machine (seqTM (emitBitsTM conjunctionTag) (CurrentDenseBuild.machine (m + 7)))) hr (by
      rintro inp work out ⟨hc, hready, hf⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨by simpa only [NetworkTallyData.headers, List.append_assoc] using hc, hready.1, hready, hf⟩) hbody
  exact hfull.consequence (by
    rintro inp work out ⟨hc, hp, hf, hb⟩
    exact ⟨hc, (OuterCurrentBankFrame.ready_and m input.length (Q.speciesCount + Q.reactionCount) Q.speciesCount Q.speciesCount
      (CurrentResources.State (m + 7) input) (OuterFuelBank.State m) work).mpr ⟨hp, hb⟩, hf⟩) (by
        rintro inp work out ⟨hc, hp, hf⟩
        have h := (OuterCurrentBankFrame.ready_and m input.length (NetworkMembership.arity Q.network) (Q.speciesCount + Q.reactionCount)
          Q.speciesCount (CurrentResources.State (m + 7) input) (OuterFuelBank.State m) work).mp hp
        exact ⟨by simpa only [NetworkCircuitBody.table, List.append_assoc] using hc, h.1, hf, h.2⟩) (by
          have hdim := NetworkCodec.decoded_dimensions_le_length hd
          have hsplit := NetworkCircuitBody.input_split input Q hd
          have hp : (NetworkTallyData.headers Q ++ NetworkCircuitBody.table Q).length ≤ input.length := by
            have hh := congrArg List.length hsplit
            simp only [List.length_append] at hh ⊢
            omega
          unfold CurrentRescan.timeBound
          simp only [conjunctionTag, List.length_cons, List.length_nil]
          omega)

end JointThermoComplexity.Complexity.OuterCurrentRescanBank

#print axioms JointThermoComplexity.Complexity.OuterCurrentRescanBank.hoareTime
