module
public import proofs.JointThermoComplexity.Complexity.ReactionPrefixTally
public import proofs.JointThermoComplexity.Complexity.UnarySeekEnd
public import proofs.JointThermoComplexity.Complexity.CountRewind

set_option autoImplicit false
@[expose] public section

/-! A canonical bounded address accumulator counts one reaction and stops before its denominator, preserving real output. -/

namespace JointThermoComplexity.Complexity.ReactionPrefixCount
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend

variable {w n : ℕ}

def machine (species : Fin w) : TM (w + 1) :=
  seqTM (UnarySeekEnd.machine destination) (seqTM (ReactionPrefixTally.machine species) (rewindWorkTM destination))

def timeBound (L : ℕ) : ℕ := 2 * L ^ 2 + 23 * L + 22

theorem hoareTime (species : Fin w) (q : ReactionCircuit.Reaction n) (L count : ℕ)
    (hn : n ≤ L) (hlen : ((DataCodec.reaction n).code q).length ≤ L)
    (hbudget : count + ExactGateCount.reactionCost q ≤ 4 * L)
    (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine species).HoareTime
      (fun inp work out => Cursor before (ReactionPrefixTally.word q ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ IsReg count (work destination) ∧ IsReg n (work species.castSucc) ∧ R (oldWork work))
      (fun inp work out => Cursor (before ++ ReactionPrefixTally.word q) tail emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ IsReg (count + ExactGateCount.reactionCost q) (work destination) ∧
        IsReg n (work species.castSucc) ∧ R (oldWork work)) (timeBound L) := by
  let S : (Fin (w + 1) → Tape) → Prop := fun work => IsReg n (oldWork work species) ∧ R (oldWork work)
  have hS : ∀ work work', (∀ j, j ≠ destination → work' j = work j) → S work → S work' := by
    intro work work' hw hp
    simpa only [S, CountOffset.oldWork_eq hw] using hp
  have hs := UnarySeekEnd.hoareTime destination count before (ReactionPrefixTally.word q ++ tail) emitted S hS
  have ht := ReactionPrefixTally.runs species q count before tail emitted R
  have hr := CountRewind.hoareTime destination (count + ExactGateCount.reactionCost q)
    (before ++ ReactionPrefixTally.word q) tail emitted S hS
  have hrest := seqTM_hoareTime (ReactionPrefixTally.machine species) (rewindWorkTM destination) ht (by
    rintro inp work out ⟨hc, hsafe, hp, hz, hspecies, hR⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hsafe, hp, hz, hspecies, hR⟩) hr
  have hfull := seqTM_hoareTime (UnarySeekEnd.machine destination)
    (seqTM (ReactionPrefixTally.machine species) (rewindWorkTM destination)) hs (by
      rintro inp work out ⟨hc, hsafe, hp, hz, hspecies, hR⟩
      obtain ⟨hi, hw, ho⟩ := hc.phase
      rw [hi, hw, ho]
      exact ⟨hc, hsafe, hp, hz, hspecies, hR⟩) hrest
  exact hfull.consequence (fun _ _ _ hp => hp)
    (fun _ _ _ ⟨hv, hc, hsafe, hspecies, hR⟩ => ⟨hc, hsafe, hv, hspecies, hR⟩) (by
      have ht := ReactionPrefixTally.decoded_bound L n ((DataCodec.reaction n).code q).length hn hlen
      unfold timeBound
      omega)

end JointThermoComplexity.Complexity.ReactionPrefixCount

#print axioms JointThermoComplexity.Complexity.ReactionPrefixCount.hoareTime
