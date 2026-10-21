module
public import proofs.JointThermoComplexity.Complexity.MotifForwardLoad
public import proofs.JointThermoComplexity.Complexity.MotifRescan

set_option autoImplicit false
@[expose] public section

/-! Retain common orientations and return to the first motif, preserving the formula prefix. -/

namespace JointThermoComplexity.Complexity.MotifForwardPreload
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts BoxBufferState BoxTraversalData

def machine (m : ℕ) : TM (m + 15) := seqTM (MotifForwardLoad.machine m) (MotifRescan.machine m)

def timeBound (L : ℕ) : ℕ := 2 * L ^ 3 + 12 * L ^ 2 + 33 * L + 28

theorem hoareTime (m idx : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ buffer m 2 → work' j = work j) → R work → R work')
    (hK : ∀ work, R work → CurrentPins.Kept m input work) :
    (machine m).HoareTime
      (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧
        BoxState.Ready m input.length idx R work)
      (fun inp work out => Cursor (MotifAccess.before Q) (NetworkTallyData.tail Q) emitted inp work out ∧
        BoxState.Ready m input.length idx R work ∧ Stored (forward Q) (work (buffer m 2))) (timeBound input.length) := by
  have hsplit : (((MotifAccess.before Q ++ FixedWordsSkip.code (motifs Q)) ++ forward Q) ++ boxes Q) = input := by
    calc _ = MotifAccess.before Q ++ NetworkTallyData.tail Q := by rw [tail_split]; simp only [List.append_assoc]
         _ = input := by simpa only [MotifAccess.before, List.append_assoc] using (MotifAccess.input_split input Q hd).symm
  have hl := MotifForwardLoad.hoareTime m idx input Q hd (MotifAccess.before Q) emitted R hR hK
  have hr := MotifRescan.hoareTime m input Q hd
    ((MotifAccess.before Q ++ FixedWordsSkip.code (motifs Q)) ++ forward Q) (boxes Q) emitted hsplit
    (fun work _ => BoxState.Ready m input.length idx R work ∧ Stored (forward Q) (work (buffer m 2)))
  have hs := seqTM_hoareTime (MotifForwardLoad.machine m) (MotifRescan.machine m) hl (by
    rintro inp work out ⟨hc, hp, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hp.1, hK work hp.2.2.2.2, hp, hf⟩) hr
  exact hs.consequence (fun _ _ _ h => h) (fun _ _ _ ⟨hc, _, _, hp, hf⟩ => ⟨hc, hp, hf⟩) (by
    unfold MotifForwardLoad.timeBound MotifAccess.timeBound timeBound
    omega)

end JointThermoComplexity.Complexity.MotifForwardPreload

#print axioms JointThermoComplexity.Complexity.MotifForwardPreload.hoareTime
