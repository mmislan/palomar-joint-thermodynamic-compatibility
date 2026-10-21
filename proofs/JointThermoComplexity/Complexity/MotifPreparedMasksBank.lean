module
public import proofs.JointThermoComplexity.Complexity.MotifPreparedMasks
public import proofs.JointThermoComplexity.Complexity.MotifBankFrame

set_option autoImplicit false
@[expose] public section

/-! Loading an actual supplied motif retains the reserved production bank and common orientations. -/

namespace JointThermoComplexity.Complexity.MotifPreparedMasksBank
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts BoxBufferState

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : NetworkData.Motif Q.speciesCount Q.reactionCount) (before tail emitted : List Bool) :
    (MotifPreparedMasks.machine (m + 5)).HoareTime
      (fun inp work out => Cursor before ((DataCodec.motif Q.speciesCount Q.reactionCount).code a ++ tail) emitted inp work out ∧
        MotifPreparedMasks.Ready (m + 5) input Q work ∧ ProductionBank.State m work)
      (fun inp work out => Cursor (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code a) tail emitted inp work out ∧
        MotifPreparedMasks.Ready (m + 5) input Q work ∧ Stored (MotifMaskData.species a) (work (buffer (m + 5) 0)) ∧
        Stored (MotifMaskData.reactions a) (work (buffer (m + 5) 1)) ∧ ProductionBank.State m work) (32 * input.length + 25) := by
  let R : (Fin (m + 20) → Tape) → Prop := fun work => MotifPreparedMasks.Metadata (m + 5) input Q work ∧ ProductionBank.State m work
  have hR : ∀ (k : Fin 2) work work', (∀ j, j ≠ buffer (m + 5) k.castSucc → work' j = work j) → R work → R work' := by
    rintro k work work' hw ⟨hm, hb⟩
    exact ⟨MotifPreparedMasks.metadata_frame (m + 5) input Q k work work' hw hm,
      MotifBankFrame.buffer_frame m k.castSucc work work' hw hb⟩
  have ht := MotifMasksLoad.hoareTime (m + 5) Q.speciesCount input Q hd a before tail emitted R hR (fun _ h => h.1.1.1)
  exact ht.consequence (by
    rintro inp work out ⟨hc, hp, hb⟩
    exact ⟨hc, (ActivityBoxBankFrame.box_ready_and m input.length Q.speciesCount
      (MotifPreparedMasks.Metadata (m + 5) input Q) (ProductionBank.State m) work).mpr ⟨hp, hb⟩⟩) (by
    rintro inp work out ⟨hc, hp, hs, hr⟩
    obtain ⟨hp', hb⟩ := (ActivityBoxBankFrame.box_ready_and m input.length Q.speciesCount
      (MotifPreparedMasks.Metadata (m + 5) input Q) (ProductionBank.State m) work).mp hp
    exact ⟨hc, hp', hs, hr, hb⟩) le_rfl

end JointThermoComplexity.Complexity.MotifPreparedMasksBank

#print axioms JointThermoComplexity.Complexity.MotifPreparedMasksBank.hoareTime
