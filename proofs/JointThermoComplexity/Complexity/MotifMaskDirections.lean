module
public import proofs.JointThermoComplexity.Complexity.MotifDecodedDirections

set_option autoImplicit false
@[expose] public section

/-! Load one actual supplied motif and emit its complete direction formula with exact decoded current indices. -/

namespace JointThermoComplexity.Complexity.MotifMaskDirections
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def machine (m : ℕ) : TM (m + 15) := seqTM (MotifPreparedMasks.machine m) (MotifDecodedDirections.machine m)

def timeBound (L : ℕ) : ℕ := 32 * L ^ 3 + 56 * L ^ 2 + 86 * L + 40

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (before tail emitted : List Bool) :
    (machine m).HoareTime
      (fun inp work out => Cursor before ((DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a) ++ tail)
        emitted inp work out ∧ MotifPreparedMasks.Ready m input Q work)
      (fun inp work out => Cursor (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a)) tail
        (emitted ++ (MotifDecodedDirections.formula Q a).code) inp work out ∧
        MotifDecodedDirections.Ready m input Q a (Q.speciesCount + Q.reactionCount) work) (timeBound input.length) := by
  have hm := MotifPreparedMasks.hoareTime m input Q hd (Q.network.motifs a) before tail emitted
  have hdirections := MotifDecodedDirections.hoareTime m input Q hd a
    (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code (Q.network.motifs a)) tail emitted
  have hs := seqTM_hoareTime (MotifPreparedMasks.machine m) (MotifDecodedDirections.machine m) hm (by
    rintro inp work out ⟨hc, hp, hspecies, hreaction⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    obtain ⟨⟨hsa, hz, hidx, hbuf, hmeta⟩, hflags⟩ := (MotifPreparedMasks.ready_iff m input Q work).mp hp
    exact ⟨hc, ⟨hsa, hz, hidx, hbuf, hmeta, hspecies⟩, hreaction, hflags⟩) hdirections
  exact hs.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by
    unfold MotifDirections.timeBound timeBound
    omega)

end JointThermoComplexity.Complexity.MotifMaskDirections

#print axioms JointThermoComplexity.Complexity.MotifMaskDirections.hoareTime
