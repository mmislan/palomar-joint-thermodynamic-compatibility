module
public import proofs.JointThermoComplexity.Complexity.MotifPreparedMasksFrame

set_option autoImplicit false
@[expose] public section

/-! Actual supplied-mask and complete direction emission retain arbitrary surrounding resources under their precise frame. -/

namespace JointThermoComplexity.Complexity.MotifMaskDirectionsFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts

theorem decoded_hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', MotifPassFrame.Unchanged m work work' → R work → R work') :
    (MotifDecodedDirections.machine m).HoareTime
      (fun inp work out => Cursor before tail emitted inp work out ∧
        MotifDecodedDirections.Ready m input Q a Q.speciesCount work ∧ R work)
      (fun inp work out => Cursor before tail (emitted ++ (MotifDecodedDirections.formula Q a).code) inp work out ∧
        MotifDecodedDirections.Ready m input Q a (Q.speciesCount + Q.reactionCount) work ∧ R work)
      (MotifDirections.timeBound input.length) := by
  let S : (Fin (m + 15) → Tape) → Prop := fun work => MotifDecodedDirections.Preserved m input Q a work ∧ R work
  have hS : ∀ work work', MotifDirectionFrame.Unchanged m work work' → S work → S work' := by
    rintro work work' hw ⟨hp, hr⟩
    exact ⟨MotifDecodedDirections.preserved_frame m input Q a work work' hw hp,
      hR work work' (MotifPassFrame.of_direction m work work' hw) hr⟩
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  have hs := MotifDirections.hoareTime m input.length Q.speciesCount (NetworkNumbering.decoded_arity_bound hd)
    (show Q.reactionCount ≤ input.length by omega) (ReactionFuel.slot m) (MotifDecodedDirections.separate m)
    (NetworkMembership.currentIndex Q.network) (fun _ => rfl)
    (fun i => decide (i ∈ (Q.network.motifs a).reactions)) Q.network.forward before tail emitted S hS
  exact hs.consequence (by
    rintro inp work out ⟨hc, ⟨hp, hm, hf⟩, hr⟩
    have hcount := (CurrentPins.counts m input Q hd work hp.2.2.2.2.1.1).2
    exact ⟨hc, (MotifPassFrame.ready_and m input.length Q.speciesCount
      (MotifDecodedDirections.Preserved m input Q a) R work).mpr ⟨hp, hr⟩,
      by simpa only [MotifMaskData.reactions_eq] using hm,
      by simpa only [MotifMaskData.forward_eq] using hf, hcount⟩) (by
    rintro inp work out ⟨hc, hp, hm, hf, _⟩
    obtain ⟨hp', hr⟩ := (MotifPassFrame.ready_and m input.length (Q.speciesCount + Q.reactionCount)
      (MotifDecodedDirections.Preserved m input Q a) R work).mp hp
    exact ⟨by simpa only [MotifDecodedDirections.dense_formula] using hc,
      ⟨hp', by simpa only [MotifMaskData.reactions_eq] using hm,
        by simpa only [MotifMaskData.forward_eq] using hf⟩, hr⟩) le_rfl

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', MotifPassFrame.Unchanged m work work' → R work → R work') :
    (MotifMaskDirections.machine m).HoareTime
      (fun inp work out => Cursor before ((DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a) ++ tail)
        emitted inp work out ∧ MotifPreparedMasks.Ready m input Q work ∧ R work)
      (fun inp work out => Cursor (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a)) tail
        (emitted ++ (MotifDecodedDirections.formula Q a).code) inp work out ∧
        MotifDecodedDirections.Ready m input Q a (Q.speciesCount + Q.reactionCount) work ∧ R work)
      (MotifMaskDirections.timeBound input.length) := by
  have hm := MotifPreparedMasksFrame.hoareTime m input Q hd (Q.network.motifs a) before tail emitted R hR
  have hdirections := decoded_hoareTime m input Q hd a
    (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a)) tail emitted R hR
  have hs := seqTM_hoareTime (MotifPreparedMasks.machine m) (MotifDecodedDirections.machine m) hm (by
    rintro inp work out ⟨hc, hp, hspecies, hreaction, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    obtain ⟨⟨hsa, hz, hidx, hbuf, hmeta⟩, hflags⟩ := (MotifPreparedMasks.ready_iff m input Q work).mp hp
    exact ⟨hc, ⟨⟨hsa, hz, hidx, hbuf, hmeta, hspecies⟩, hreaction, hflags⟩, hr⟩) hdirections
  exact hs.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by
    unfold MotifDirections.timeBound MotifMaskDirections.timeBound
    omega)

end JointThermoComplexity.Complexity.MotifMaskDirectionsFrame

#print axioms JointThermoComplexity.Complexity.MotifMaskDirectionsFrame.decoded_hoareTime
#print axioms JointThermoComplexity.Complexity.MotifMaskDirectionsFrame.hoareTime
