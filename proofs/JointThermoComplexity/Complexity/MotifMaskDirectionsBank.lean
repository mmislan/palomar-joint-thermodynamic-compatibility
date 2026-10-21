module
public import proofs.JointThermoComplexity.Complexity.MotifMaskDirections
public import proofs.JointThermoComplexity.Complexity.MotifPreparedMasksBank

set_option autoImplicit false
@[expose] public section

/-! Exact supplied-motif direction emission retains the production bank, without changing output or time. -/

namespace JointThermoComplexity.Complexity.MotifMaskDirectionsBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts

theorem decoded_hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before tail emitted : List Bool) :
    (MotifDecodedDirections.machine (m + 5)).HoareTime
      (fun inp work out => Cursor before tail emitted inp work out ∧
        MotifDecodedDirections.Ready (m + 5) input Q a Q.speciesCount work ∧ ProductionBank.State m work)
      (fun inp work out => Cursor before tail (emitted ++ (MotifDecodedDirections.formula Q a).code) inp work out ∧
        MotifDecodedDirections.Ready (m + 5) input Q a (Q.speciesCount + Q.reactionCount) work ∧ ProductionBank.State m work)
      (MotifDirections.timeBound input.length) := by
  let R : (Fin (m + 20) → Tape) → Prop := fun work => MotifDecodedDirections.Preserved (m + 5) input Q a work ∧ ProductionBank.State m work
  have hR : ∀ work work', MotifDirectionFrame.Unchanged (m + 5) work work' → R work → R work' := by
    rintro work work' hw ⟨hp, hb⟩
    exact ⟨MotifDecodedDirections.preserved_frame (m + 5) input Q a work work' hw hp,
      MotifBankFrame.direction_frame m work work' hw hb⟩
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  have hs := MotifDirections.hoareTime (m + 5) input.length Q.speciesCount (NetworkNumbering.decoded_arity_bound hd)
    (show Q.reactionCount ≤ input.length by omega) (ReactionFuel.slot (m + 5)) (MotifDecodedDirections.separate (m + 5))
    (NetworkMembership.currentIndex Q.network) (fun _ => rfl)
    (fun i => decide (i ∈ (Q.network.motifs a).reactions)) Q.network.forward before tail emitted R hR
  exact hs.consequence (by
    rintro inp work out ⟨hc, ⟨hp, hm, hf⟩, hb⟩
    have hcount := (CurrentPins.counts (m + 5) input Q hd work hp.2.2.2.2.1.1).2
    exact ⟨hc, (ActivityBoxBankFrame.box_ready_and m input.length Q.speciesCount
      (MotifDecodedDirections.Preserved (m + 5) input Q a) (ProductionBank.State m) work).mpr ⟨hp, hb⟩,
      by simpa only [MotifMaskData.reactions_eq] using hm,
      by simpa only [MotifMaskData.forward_eq] using hf, hcount⟩) (by
    rintro inp work out ⟨hc, hp, hm, hf, _⟩
    obtain ⟨hp', hb⟩ := (ActivityBoxBankFrame.box_ready_and m input.length (Q.speciesCount + Q.reactionCount)
      (MotifDecodedDirections.Preserved (m + 5) input Q a) (ProductionBank.State m) work).mp hp
    exact ⟨by simpa only [MotifDecodedDirections.dense_formula] using hc,
      ⟨hp', by simpa only [MotifMaskData.reactions_eq] using hm,
        by simpa only [MotifMaskData.forward_eq] using hf⟩, hb⟩) le_rfl

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before tail emitted : List Bool) :
    (MotifMaskDirections.machine (m + 5)).HoareTime
      (fun inp work out => Cursor before ((DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a) ++ tail)
        emitted inp work out ∧ MotifPreparedMasks.Ready (m + 5) input Q work ∧ ProductionBank.State m work)
      (fun inp work out => Cursor (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a)) tail
        (emitted ++ (MotifDecodedDirections.formula Q a).code) inp work out ∧
        MotifDecodedDirections.Ready (m + 5) input Q a (Q.speciesCount + Q.reactionCount) work ∧ ProductionBank.State m work)
      (MotifMaskDirections.timeBound input.length) := by
  have hm := MotifPreparedMasksBank.hoareTime m input Q hd (Q.network.motifs a) before tail emitted
  have hdirections := decoded_hoareTime m input Q hd a
    (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a)) tail emitted
  have hs := seqTM_hoareTime (MotifPreparedMasks.machine (m + 5)) (MotifDecodedDirections.machine (m + 5)) hm (by
    rintro inp work out ⟨hc, hp, hspecies, hreaction, hbank⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    obtain ⟨⟨hsa, hz, hidx, hbuf, hmeta⟩, hflags⟩ := (MotifPreparedMasks.ready_iff (m + 5) input Q work).mp hp
    exact ⟨hc, ⟨⟨hsa, hz, hidx, hbuf, hmeta, hspecies⟩, hreaction, hflags⟩, hbank⟩) hdirections
  exact hs.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by
    unfold MotifDirections.timeBound MotifMaskDirections.timeBound
    omega)

end JointThermoComplexity.Complexity.MotifMaskDirectionsBank

#print axioms JointThermoComplexity.Complexity.MotifMaskDirectionsBank.decoded_hoareTime
#print axioms JointThermoComplexity.Complexity.MotifMaskDirectionsBank.hoareTime
