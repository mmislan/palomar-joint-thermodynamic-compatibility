module
public import proofs.JointThermoComplexity.Complexity.ReactionArrayTally
public import proofs.JointThermoComplexity.Complexity.NetworkTallyData

set_option autoImplicit false
@[expose] public section

/-! Read dimensions and reactions to accumulate the exact circuit gate count. -/

namespace JointThermoComplexity.Complexity.NetworkTally
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend NetworkTallyData

variable {w : ℕ}

def machine (species reactions : Fin w) : TM (w + 1) :=
  seqTM DimensionSkip.machine (ReactionArrayTally.machine species reactions)

def timeBound (Q : NetworkCodec.Input) : ℕ :=
  Q.speciesCount + Q.reactionCount + Q.coreCount + 5 + 1 +
    (Q.reactionCount * (ReactionTally.timeBound Q.speciesCount (ReactionArrayData.code (NetworkTallyData.reactions Q)).length + 2) +
      (Q.reactionCount + 2))

theorem hoareTime (species reactionFuel : Fin w) (hsr : species ≠ reactionFuel) (Q : NetworkCodec.Input)
    (count : ℕ) (before extra emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine species reactionFuel).HoareTime
      (fun inp work out => IsReg Q.reactionCount (work reactionFuel.castSucc) ∧ IsReg Q.speciesCount (work species.castSucc) ∧
        Cursor before (Q.code ++ extra) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate count true) ∧ (work destination).cells 0 = Γ.start ∧ R (oldWork work))
      (fun inp work out => IsReg Q.reactionCount (work reactionFuel.castSucc) ∧ IsReg Q.speciesCount (work species.castSucc) ∧
        Cursor (before ++ (headers Q ++ ReactionArrayData.code (NetworkTallyData.reactions Q))) (tail Q ++ extra) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧
        (work destination).HasBinaryPrefix (List.replicate (count + NetworkMembership.gates Q.network) true) ∧
        (work destination).cells 0 = Γ.start ∧ R (oldWork work)) (timeBound Q) := by
  let RP : (Fin (w + 1) → Tape) → Prop := fun work =>
    IsReg Q.reactionCount (work reactionFuel.castSucc) ∧ IsReg Q.speciesCount (work species.castSucc) ∧
      (work destination).HasBinaryPrefix (List.replicate count true) ∧ (work destination).cells 0 = Γ.start ∧ R (oldWork work)
  have hheaders := DimensionSkip.hoareTime Q.speciesCount Q.reactionCount Q.coreCount before
    (ReactionArrayData.code (NetworkTallyData.reactions Q) ++ (tail Q ++ extra)) emitted RP
  have hrecords := ReactionArrayTally.hoareTime species reactionFuel hsr (NetworkTallyData.reactions Q)
    count (before ++ headers Q) (tail Q ++ extra) emitted R
  have hseq := seqTM_hoareTime DimensionSkip.machine (ReactionArrayTally.machine species reactionFuel) hheaders (by
    rintro inp work out ⟨hc, hs, hr, hn, hp, hz, hR⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [reaction_count] using hr, hn, hc, hs, hp, hz, hR⟩) hrecords
  exact hseq.consequence
    (fun _ _ _ ⟨hr, hn, hc, hs, hp, hz, hR⟩ =>
      ⟨by simpa only [code_split, headers, List.append_assoc] using hc, hs, hr, hn, hp, hz, hR⟩)
    (fun _ _ _ hp => by simpa only [reaction_count, gate_count, List.append_assoc] using hp)
    (by simp only [timeBound, reaction_count]; exact le_rfl)

end JointThermoComplexity.Complexity.NetworkTally

#print axioms JointThermoComplexity.Complexity.NetworkTally.hoareTime
