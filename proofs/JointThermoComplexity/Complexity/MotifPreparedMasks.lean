module
public import proofs.JointThermoComplexity.Complexity.MotifMasksLoad

set_option autoImplicit false
@[expose] public section

/-! Load a supplied core's masks while retaining validated metadata and the common orientation vector. -/

namespace JointThermoComplexity.Complexity.MotifPreparedMasks
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts BoxBufferState

def Metadata (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (work : Fin (m + 15) → Tape) : Prop :=
  MotifBufferMeta.State m input work ∧ Stored (BoxTraversalData.forward Q) (work (buffer m 2))

def Ready (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (work : Fin (m + 15) → Tape) : Prop :=
  BoxState.Ready m input.length Q.speciesCount (Metadata m input Q) work

theorem metadata_frame (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (k : Fin 2)
    (work work' : Fin (m + 15) → Tape) (hw : ∀ j, j ≠ buffer m k.castSucc → work' j = work j) :
    Metadata m input Q work → Metadata m input Q work' := by
  have hne : buffer m 2 ≠ buffer m k.castSucc := by
    intro he
    have hv := congrArg Fin.val he
    change 2 + 2 = k.val + 2 at hv
    have hk := k.isLt
    omega
  rintro ⟨hm, hf⟩
  exact ⟨MotifBufferMeta.frame m input k.castSucc work work' hw hm, by simpa only [hw _ hne] using hf⟩

theorem ready_iff (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (work : Fin (m + 15) → Tape) :
    Ready m input Q work ↔ BoxState.Ready m input.length Q.speciesCount (MotifBufferMeta.State m input) work ∧
      Stored (BoxTraversalData.forward Q) (work (buffer m 2)) := by
  constructor
  · rintro ⟨hs, hz, hi, hb, hm, hf⟩
    exact ⟨⟨hs, hz, hi, hb, hm⟩, hf⟩
  · rintro ⟨⟨hs, hz, hi, hb, hm⟩, hf⟩
    exact ⟨hs, hz, hi, hb, hm, hf⟩

abbrev machine (m : ℕ) : TM (m + 15) := MotifMasksLoad.machine m

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : NetworkData.Motif Q.speciesCount Q.reactionCount) (before tail emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor before ((DataCodec.motif Q.speciesCount Q.reactionCount).code a ++ tail) emitted inp work out ∧
        Ready m input Q work)
      (fun inp work out => Cursor (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code a) tail emitted inp work out ∧
        Ready m input Q work ∧ Stored (MotifMaskData.species a) (work (buffer m 0)) ∧
        Stored (MotifMaskData.reactions a) (work (buffer m 1))) (32 * input.length + 25) :=
  MotifMasksLoad.hoareTime m Q.speciesCount input Q hd a before tail emitted (Metadata m input Q)
    (metadata_frame m input Q) (fun _ h => h.1.1)

end JointThermoComplexity.Complexity.MotifPreparedMasks

#print axioms JointThermoComplexity.Complexity.MotifPreparedMasks.metadata_frame
#print axioms JointThermoComplexity.Complexity.MotifPreparedMasks.ready_iff
#print axioms JointThermoComplexity.Complexity.MotifPreparedMasks.hoareTime
