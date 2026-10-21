module
public import proofs.JointThermoComplexity.Complexity.CurrentRecord
public import proofs.JointThermoComplexity.Complexity.CurrentReady

set_option autoImplicit false
@[expose] public section

/-! Consume one actual reaction, emit its current equation and advance the retained current-variable cursor. -/

namespace JointThermoComplexity.Complexity.CurrentStep
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts CurrentReady

def machine (m : ℕ) : TM (m + 15) := seqTM (CurrentRecord.machine m) (UnarySuccessor.machine (species (m + 1)))

def timeBound (L : ℕ) : ℕ := 66 * L ^ 2 + 164 * L + 120

theorem hoareTime {n arity : ℕ} (m L count : ℕ) (q : ReactionCircuit.Reaction n) (current result : Fin arity)
    (ha : arity ≤ 4 * L) (hn : n ≤ L) (hlen : ((DataCodec.reaction n).code q).length ≤ L)
    (hresult : result.val + 1 = count + ExactGateCount.reactionCost q)
    (before tail emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ raw m → j ≠ previous (m + 1) → j ≠ species (m + 1) →
      work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before ((DataCodec.reaction n).code q ++ tail) emitted inp work out ∧
        Ready m L count current.val n R work)
      (fun inp work out => Cursor (before ++ (DataCodec.reaction n).code q) tail
        (emitted ++ CurrentRecord.word q current result) inp work out ∧
        Ready m L (count + ExactGateCount.reactionCost q) (current.val + 1) n R work) (timeBound L) := by
  intro inp work out hp
  rcases hp with ⟨hc, hs, hz, hv, hi, ⟨old, hold, hprev⟩, hf, hr⟩
  have hrec := CurrentRecord.hoareTime m L count old q current result ha hn hold hlen hresult before tail emitted R
    (fun work work' hw hp => hR work work' (fun j hraw hprev _ => hw j hraw hprev) hp)
  let S : (Fin (m + 15) → Tape) → Prop := fun work =>
    BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
    IsReg (count + ExactGateCount.reactionCost q) (work (raw m)) ∧ IsReg result.val (work (previous (m + 1))) ∧
    IsReg n (work (MonomialFuel.slot (m + 1))) ∧ R work
  have hS : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → S work → S work' := by
    rintro work work' hw ⟨hz, hv, hp, hf, hr⟩
    exact ⟨by simpa only [hw _ (species_ne_scratch (m + 1)).symm] using hz,
      by simpa only [hw _ (raw_ne_current m)] using hv,
      by simpa only [hw _ (previous_ne_species (m + 1))] using hp,
      by simpa only [hw _ (MonomialFuel.slot_separate (m + 1)).species] using hf,
      hR work work' (fun j _ _ hj => hw j hj) hr⟩
  have hsucc := UnarySuccessor.hoareTime (species (m + 1)) current.val
    (before ++ (DataCodec.reaction n).code q) tail (emitted ++ CurrentRecord.word q current result) S hS
  have hseq := seqTM_hoareTime (CurrentRecord.machine m) (UnarySuccessor.machine (species (m + 1))) hrec (by
    rintro inp work out ⟨hc, hs, hz, hv, hp, hi, hf, hr⟩
    obtain ⟨hip, hw, ho⟩ := hc.phase
    rw [hip, hw, ho]
    exact ⟨hc, hs, hi, hz, hv, hp, hf, hr⟩) hsucc
  obtain ⟨d, t, ht, hreach, hhalt, hdc, hds, hdi, hdz, hdv, hdp, hdf, hdr⟩ :=
    hseq inp work out ⟨hc, hs, hz, hv, hprev, hi, hf, hr⟩
  refine ⟨d, t, ?_, hreach, hhalt, hdc, hds, hdz, hdv, hdi,
    ⟨result.val, result.isLt.le.trans ha, hdp⟩, hdf, hdr⟩
  have hi := current.isLt
  unfold timeBound CurrentRecord.timeBound at *
  omega

end JointThermoComplexity.Complexity.CurrentStep

#print axioms JointThermoComplexity.Complexity.CurrentStep.hoareTime
