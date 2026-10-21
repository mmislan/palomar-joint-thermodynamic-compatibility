module
public import proofs.JointThermoComplexity.Complexity.NetworkTally
public import proofs.JointThermoComplexity.Complexity.CountRewind
public import proofs.JointThermoComplexity.Complexity.InputRewind

set_option autoImplicit false
@[expose] public section

/-! Prepare the canonical circuit-count register, then restart input with the formula output unchanged. -/

namespace JointThermoComplexity.Complexity.NetworkGateCount
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountAppend NetworkTallyData

variable {w : ℕ}

def scanned (Q : NetworkCodec.Input) : List Bool := headers Q ++ ReactionArrayData.code (reactions Q)

def machine (species reactionFuel : Fin w) : TM (w + 1) :=
  seqTM (seqTM (NetworkTally.machine species reactionFuel) (rewindWorkTM destination)) rewindInputTM

def timeBound (Q : NetworkCodec.Input) : ℕ :=
  NetworkTally.timeBound Q + 1 + (NetworkMembership.gates Q.network + 3) + 1 + ((scanned Q).length + 3)

theorem hoareTime (species reactionFuel : Fin w) (hsr : species ≠ reactionFuel) (Q : NetworkCodec.Input)
    (extra emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine species reactionFuel).HoareTime
      (fun inp work out => IsReg Q.reactionCount (work reactionFuel.castSucc) ∧ IsReg Q.speciesCount (work species.castSucc) ∧
        Cursor [] (Q.code ++ extra) emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg 0 (work destination) ∧ R (oldWork work))
      (fun inp work out => IsReg (NetworkMembership.gates Q.network) (work destination) ∧
        IsReg Q.reactionCount (work reactionFuel.castSucc) ∧ IsReg Q.speciesCount (work species.castSucc) ∧
        Cursor [] (Q.code ++ extra) emitted inp work out ∧ (∀ j, Parked (work j)) ∧ R (oldWork work)) (timeBound Q) := by
  let RP : (Fin (w + 1) → Tape) → Prop := fun work =>
    IsReg Q.reactionCount (oldWork work reactionFuel) ∧ IsReg Q.speciesCount (oldWork work species) ∧ R (oldWork work)
  have hRP : ∀ work work', (∀ j, j ≠ destination → work' j = work j) → RP work → RP work' := by
    intro work work' hw hp
    change IsReg Q.reactionCount (oldWork work' reactionFuel) ∧ IsReg Q.speciesCount (oldWork work' species) ∧ R (oldWork work')
    rw [CountOffset.oldWork_eq hw]
    exact hp
  have htally := NetworkTally.hoareTime species reactionFuel hsr Q 0 [] extra emitted R
  have hrew := CountRewind.hoareTime destination (NetworkMembership.gates Q.network)
    (scanned Q) (tail Q ++ extra) emitted RP hRP
  have hcount := seqTM_hoareTime (NetworkTally.machine species reactionFuel) (rewindWorkTM destination) htally (by
    rintro inp work out ⟨hr, hn, hc, hs, hp, hz, hR⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨by simpa only [scanned, List.nil_append] using hc, hs,
      by simpa only [Nat.zero_add] using hp, hz, hr, hn, hR⟩) hrew
  let RF : (Fin (w + 1) → Tape) → Prop := fun work =>
    IsReg (NetworkMembership.gates Q.network) (work destination) ∧ (∀ j, Parked (work j)) ∧ RP work
  have hinput := InputRewind.hoareTime (scanned Q) (tail Q ++ extra) emitted RF
  have hfull := seqTM_hoareTime (seqTM (NetworkTally.machine species reactionFuel) (rewindWorkTM destination))
      rewindInputTM hcount (by
        rintro inp work out ⟨hg, hc, hs, hp⟩
        obtain ⟨hi, hw, ho⟩ := hc.phase
        rw [hi, hw, ho]
        exact ⟨hc, hg, hs, hp⟩) hinput
  exact hfull.consequence
    (fun _ _ _ ⟨hr, hn, hc, hs, hg, hR⟩ => ⟨hr, hn, hc, hs, CountTape.empty_prefix_of_zero hg, hg.cell0, hR⟩)
    (fun _ _ _ ⟨hc, hg, hs, hr, hn, hR⟩ => ⟨hg, hr, hn,
      by simpa only [scanned, code_split, List.append_assoc] using hc, hs, hR⟩) le_rfl

end JointThermoComplexity.Complexity.NetworkGateCount

#print axioms JointThermoComplexity.Complexity.NetworkGateCount.hoareTime
