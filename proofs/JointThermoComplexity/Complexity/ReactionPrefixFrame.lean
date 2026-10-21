module
public import proofs.JointThermoComplexity.Complexity.ReactionPrefixCount

set_option autoImplicit false
@[expose] public section

/-! Expose the canonical partial tally with an arbitrary surrounding predicate stable outside its accumulator. -/

namespace JointThermoComplexity.Complexity.ReactionPrefixFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend

variable {w n : ℕ}

theorem outside_eq (work work' : Fin (w + 1) → Tape) (h : oldWork work' = oldWork work)
    (j : Fin (w + 1)) (hj : j ≠ destination) : work' j = work j := by
  have hi : j.val < w := by
    have hl := j.isLt
    by_contra hn
    have he : j = destination := by apply Fin.ext; change j.val = w; omega
    exact hj he
  exact congrFun h ⟨j.val, hi⟩

theorem hoareTime (species : Fin w) (q : ReactionCircuit.Reaction n) (L count : ℕ)
    (hn : n ≤ L) (hlen : ((DataCodec.reaction n).code q).length ≤ L)
    (hbudget : count + ExactGateCount.reactionCost q ≤ 4 * L)
    (before tail emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ destination → work' j = work j) → R work → R work') :
    (ReactionPrefixCount.machine species).HoareTime
      (fun inp work out => Cursor before (ReactionPrefixTally.word q ++ tail) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ IsReg count (work destination) ∧ IsReg n (work species.castSucc) ∧ R work)
      (fun inp work out => Cursor (before ++ ReactionPrefixTally.word q) tail emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ IsReg (count + ExactGateCount.reactionCost q) (work destination) ∧
        IsReg n (work species.castSucc) ∧ R work) (ReactionPrefixCount.timeBound L) := by
  rintro inp work out ⟨hc, hs, hv, hf, hr⟩
  have ht := ReactionPrefixCount.hoareTime species q L count hn hlen hbudget before tail emitted
    (fun old => old = oldWork work)
  obtain ⟨d, t, htime, hreach, hhalt, hdc, hds, hdv, hdf, hdo⟩ := ht inp work out ⟨hc, hs, hv, hf, rfl⟩
  exact ⟨d, t, htime, hreach, hhalt, hdc, hds, hdv, hdf,
    hR work d.work (outside_eq work d.work hdo) hr⟩

end JointThermoComplexity.Complexity.ReactionPrefixFrame

#print axioms JointThermoComplexity.Complexity.ReactionPrefixFrame.hoareTime
