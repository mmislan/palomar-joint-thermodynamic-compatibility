module
public import proofs.JointThermoComplexity.Complexity.BoxTraversalData

set_option autoImplicit false
@[expose] public section

/-! Actual read-only traversal from the reaction-table exit to the optional-box array. -/

namespace JointThermoComplexity.Complexity.BoxTraversal
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BoxTraversalData

variable {w : ℕ}

def machine (width cores reactions : Fin w) : TM w :=
  seqTM (FixedWordsSkip.machine width cores) (BooleanWordSkip.machine reactions)

def timeBound (n r c : ℕ) : ℕ := FixedWordsSkip.timeBound (n + r) c + 4 * r + 3

theorem hoareTime (width cores reactions : Fin w) (hne : width ≠ cores) (Q : NetworkCodec.Input)
    (before emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine width cores reactions).HoareTime
      (fun inp work out => Cursor before (NetworkTallyData.tail Q) emitted inp work out ∧
        IsReg Q.coreCount (work cores) ∧ IsReg (Q.speciesCount + Q.reactionCount) (work width) ∧
        IsReg Q.reactionCount (work reactions) ∧ R work out)
      (fun inp work out => Cursor ((before ++ FixedWordsSkip.code (motifs Q)) ++ forward Q) (boxes Q) emitted inp work out ∧
        IsReg Q.coreCount (work cores) ∧ IsReg (Q.speciesCount + Q.reactionCount) (work width) ∧
        IsReg Q.reactionCount (work reactions) ∧ R work out)
      (timeBound Q.speciesCount Q.reactionCount Q.coreCount) := by
  have hm := FixedWordsSkip.hoareTime width cores hne (Q.speciesCount + Q.reactionCount) (motifs Q)
    (motifs_width Q) before (forward Q ++ boxes Q) emitted
    (fun work out => IsReg Q.reactionCount (work reactions) ∧ R work out)
  have hf := BooleanWordSkip.hoareTime reactions (forward Q)
    (before ++ FixedWordsSkip.code (motifs Q)) (boxes Q) emitted
    (fun work out => IsReg Q.coreCount (work cores) ∧
      IsReg (Q.speciesCount + Q.reactionCount) (work width) ∧ R work out)
  have hs := seqTM_hoareTime (FixedWordsSkip.machine width cores) (BooleanWordSkip.machine reactions) hm (by
    rintro inp work out ⟨hc, hcore, hwidth, hreaction, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, by simpa only [forward_length] using hreaction,
      by simpa only [motifs_count] using hcore, hwidth, hr⟩) hf
  exact hs.consequence (by
    rintro inp work out ⟨hc, hcore, hwidth, hreaction, hr⟩
    exact ⟨by simpa only [tail_split] using hc,
      by simpa only [motifs_count] using hcore, hwidth, hreaction, hr⟩) (by
        rintro inp work out ⟨hc, hreaction, hcore, hwidth, hr⟩
        exact ⟨hc, hcore, hwidth, by simpa only [forward_length] using hreaction, hr⟩) (by
          simp only [motifs_count, forward_length]
          unfold timeBound
          omega)

end JointThermoComplexity.Complexity.BoxTraversal

#print axioms JointThermoComplexity.Complexity.BoxTraversal.hoareTime
