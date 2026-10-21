module
public import proofs.JointThermoComplexity.Complexity.MotifPassFrame

set_option autoImplicit false
@[expose] public section

/-! The unchanged supplied-mask loader retains any surrounding data respecting its actual work frame. -/

namespace JointThermoComplexity.Complexity.MotifPreparedMasksFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts BoxBufferState

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : NetworkData.Motif Q.speciesCount Q.reactionCount) (before tail emitted : List Bool)
    (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', MotifPassFrame.Unchanged m work work' → R work → R work') :
    (MotifPreparedMasks.machine m).HoareTime
      (fun inp work out => Cursor before ((DataCodec.motif Q.speciesCount Q.reactionCount).code a ++ tail) emitted inp work out ∧
        MotifPreparedMasks.Ready m input Q work ∧ R work)
      (fun inp work out => Cursor (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code a) tail emitted inp work out ∧
        MotifPreparedMasks.Ready m input Q work ∧ Stored (MotifMaskData.species a) (work (buffer m 0)) ∧
        Stored (MotifMaskData.reactions a) (work (buffer m 1)) ∧ R work) (32 * input.length + 25) := by
  let S : (Fin (m + 15) → Tape) → Prop := fun work => MotifPreparedMasks.Metadata m input Q work ∧ R work
  have hS : ∀ (k : Fin 2) work work', (∀ j, j ≠ buffer m k.castSucc → work' j = work j) → S work → S work' := by
    rintro k work work' hw ⟨hm, hr⟩
    exact ⟨MotifPreparedMasks.metadata_frame m input Q k work work' hw hm,
      hR work work' (MotifPassFrame.of_mask m k work work' hw) hr⟩
  have ht := MotifMasksLoad.hoareTime m Q.speciesCount input Q hd a before tail emitted S hS (fun _ h => h.1.1.1)
  exact ht.consequence (by
    rintro inp work out ⟨hc, hp, hr⟩
    exact ⟨hc, (MotifPassFrame.ready_and m input.length Q.speciesCount
      (MotifPreparedMasks.Metadata m input Q) R work).mpr ⟨hp, hr⟩⟩) (by
    rintro inp work out ⟨hc, hp, hs, hm⟩
    obtain ⟨hp', hr⟩ := (MotifPassFrame.ready_and m input.length Q.speciesCount
      (MotifPreparedMasks.Metadata m input Q) R work).mp hp
    exact ⟨hc, hp', hs, hm, hr⟩) le_rfl

end JointThermoComplexity.Complexity.MotifPreparedMasksFrame

#print axioms JointThermoComplexity.Complexity.MotifPreparedMasksFrame.hoareTime
