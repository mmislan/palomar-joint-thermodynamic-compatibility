module
public import proofs.JointThermoComplexity.Complexity.MotifVectorLoad
public import proofs.JointThermoComplexity.Complexity.MotifMaskData
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! Traverse supplied motif records and retain the actual shared orientation vector in buffer four. -/

namespace JointThermoComplexity.Complexity.MotifForwardLoad
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifBufferPorts BoxBufferState BoxTraversalData

def coreFuel (m : ℕ) : Fin (m + 15) := RoutedNetworkParser.count (m + 9) 2

def machine (m : ℕ) : TM (m + 15) := seqTM
  (FixedWordsSkip.machine (CountLayout.offset (m + 7)) (coreFuel m)) (MotifVectorLoad.machine m 2 false)

def timeBound (L : ℕ) : ℕ := 4 * L ^ 2 + 21 * L + 15

theorem runtime_bound (L width count : ℕ) (hw : width ≤ L) (hc : count ≤ L) :
    FixedWordsSkip.timeBound width count + (16 * L + 12) + 1 ≤ timeBound L := by
  unfold FixedWordsSkip.timeBound timeBound
  calc count * (4 * width + 4) + (count + 2) + (16 * L + 12) + 1 ≤
       L * (4 * L + 4) + (L + 2) + (16 * L + 12) + 1 := by
        have hm := Nat.mul_le_mul hc (show 4 * width + 4 ≤ 4 * L + 4 by omega)
        omega
       _ = _ := by ring1

theorem hoareTime (m idx : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (before emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ buffer m 2 → work' j = work j) → R work → R work')
    (hK : ∀ work, R work → CurrentPins.Kept m input work) :
    (machine m).HoareTime
      (fun inp work out => Cursor before (NetworkTallyData.tail Q) emitted inp work out ∧ BoxState.Ready m input.length idx R work)
      (fun inp work out => Cursor ((before ++ FixedWordsSkip.code (motifs Q)) ++ forward Q) (boxes Q) emitted inp work out ∧
        BoxState.Ready m input.length idx R work ∧ Stored (forward Q) (work (buffer m 2))) (timeBound input.length) := by
  have hne : CountLayout.offset (m + 7) ≠ coreFuel m := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = m + 9 + 1 + 2 at hv
    omega
  have hdim := DecodedDimensions.decode_counts hd
  have hoff : ArityValue.offset input = Q.speciesCount + Q.reactionCount := by
    simp only [ArityValue.offset, hdim.1, hdim.2.1]
  have hm := FixedWordsSkip.hoareTime (CountLayout.offset (m + 7)) (coreFuel m) hne
    (Q.speciesCount + Q.reactionCount) (motifs Q) (motifs_width Q) before (forward Q ++ boxes Q) emitted
    (fun work _ => BoxState.Ready m input.length idx R work)
  have hf := MotifVectorLoad.hoareTime m idx input Q hd 2 false (forward Q)
    (before ++ FixedWordsSkip.code (motifs Q)) (boxes Q) emitted (forward_length Q) R hR hK
  have hs := seqTM_hoareTime (FixedWordsSkip.machine (CountLayout.offset (m + 7)) (coreFuel m))
    (MotifVectorLoad.machine m 2 false) hm (by
      rintro inp work out ⟨hc, _, _, hp⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hp⟩) hf
  exact hs.consequence (by
    rintro inp work out ⟨hc, hp⟩
    have hk := hK work hp.2.2.2.2
    have hcounts := ParserRegisters.decoded_counts (m + 9) input (CountAppend.oldWork work) hk.2.2 hd
    exact ⟨by simpa only [tail_split] using hc,
      by simpa only [motifs_count, coreFuel, CountAppend.oldWork, RoutedNetworkParser.count] using hcounts.2.2,
      by simpa only [hoff] using hk.1, hp⟩)
    (fun _ _ _ hp => hp) (by
      rw [motifs_count]
      have hb := NetworkCodec.decoded_dimensions_le_length hd
      have ht := runtime_bound input.length (Q.speciesCount + Q.reactionCount) Q.coreCount (by omega) (by omega)
      omega)

end JointThermoComplexity.Complexity.MotifForwardLoad

#print axioms JointThermoComplexity.Complexity.MotifForwardLoad.runtime_bound
#print axioms JointThermoComplexity.Complexity.MotifForwardLoad.hoareTime
