module
public import proofs.JointThermoComplexity.Complexity.MotifVectorLoad
public import proofs.JointThermoComplexity.Complexity.MotifMaskData

set_option autoImplicit false
@[expose] public section

/-! Consume one actual supplied motif record and retain its two membership vectors separately. -/

namespace JointThermoComplexity.Complexity.MotifMasksLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts BoxBufferState MotifMaskData

def machine (m : ℕ) : TM (m + 15) := seqTM (MotifVectorLoad.machine m 0 true) (MotifVectorLoad.machine m 1 false)

theorem hoareTime (m idx : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : NetworkData.Motif Q.speciesCount Q.reactionCount) (before tail emitted : List Bool)
    (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ k : Fin 2, ∀ work work', (∀ j, j ≠ buffer m k.castSucc → work' j = work j) → R work → R work')
    (hK : ∀ work, R work → CurrentPins.Kept m input work) :
    (machine m).HoareTime
      (fun inp work out => Cursor before ((DataCodec.motif Q.speciesCount Q.reactionCount).code a ++ tail) emitted inp work out ∧
        BoxState.Ready m input.length idx R work)
      (fun inp work out => Cursor (before ++ (DataCodec.motif Q.speciesCount Q.reactionCount).code a) tail emitted inp work out ∧
        BoxState.Ready m input.length idx R work ∧ Stored (species a) (work (buffer m 0)) ∧
        Stored (reactions a) (work (buffer m 1))) (32 * input.length + 25) := by
  have hne : buffer m 0 ≠ buffer m 1 := by
    intro he
    have hv := congrArg Fin.val he
    change (2 : ℕ) = 3 at hv
    omega
  let S : (Fin (m + 15) → Tape) → Prop := fun work => R work ∧ Stored (species a) (work (buffer m 0))
  have hS : ∀ work work', (∀ j, j ≠ buffer m 1 → work' j = work j) → S work → S work' := by
    rintro work work' hw ⟨hr, hs⟩
    exact ⟨hR 1 work work' hw hr, by simpa only [hw _ hne] using hs⟩
  have hspecies := MotifVectorLoad.hoareTime m idx input Q hd 0 true (species a) before (reactions a ++ tail) emitted
    (species_length a) R (hR 0) hK
  have hreaction := MotifVectorLoad.hoareTime m idx input Q hd 1 false (reactions a) (before ++ species a) tail emitted
    (reactions_length a) S hS (fun work hs => hK work hs.1)
  have hs := seqTM_hoareTime (MotifVectorLoad.machine m 0 true) (MotifVectorLoad.machine m 1 false) hspecies (by
    rintro inp work out ⟨hc, hp, hstored⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    rcases hp with ⟨hsafe, hz, hidx, hbuffers, hr⟩
    exact ⟨hc, hsafe, hz, hidx, hbuffers, hr, hstored⟩) hreaction
  exact hs.consequence
    (fun _ _ _ h => by simpa only [motif_code, List.append_assoc] using h) (by
      rintro inp work out ⟨hc, ⟨hsafe, hz, hidx, hbuffers, hr, hspecies⟩, hreaction⟩
      exact ⟨by simpa only [motif_code, List.append_assoc] using hc,
        ⟨hsafe, hz, hidx, hbuffers, hr⟩, hspecies, hreaction⟩) (by omega)

end JointThermoComplexity.Complexity.MotifMasksLoad

#print axioms JointThermoComplexity.Complexity.MotifMasksLoad.hoareTime
