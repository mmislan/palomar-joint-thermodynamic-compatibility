module
public import proofs.JointThermoComplexity.Complexity.MotifPrefixData
public import proofs.JointThermoComplexity.Complexity.MotifAccessCursor
public import proofs.JointThermoComplexity.Complexity.ProductionPorts
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! Recover the actual supplied-motif cursor from the stored core index while preserving all work and output. -/

namespace JointThermoComplexity.Complexity.MotifIndexedAccess
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

def species (m : ℕ) : Fin (m + 22) := ProductionPorts.count (m + 2)
def reactions (m : ℕ) : Fin (m + 22) := ReactionFuel.slot (m + 7)
def core (m : ℕ) : Fin (m + 22) := ProductionPorts.core (m + 2)

def machine (m : ℕ) : TM (m + 22) := seqTM (MotifAccess.machine (m + 7))
  (MotifPrefixSkip.machine (species m) (reactions m) (core m))

def timeBound (L : ℕ) : ℕ := 2 * L ^ 3 + 12 * L ^ 2 + 20 * L + 15

theorem prefix_runtime_bound (L n r ci : ℕ) (hnr : n + r ≤ L) (hci : ci ≤ L) :
    MotifPrefixSkip.timeBound n r ci ≤ 4 * L ^ 2 + 8 * L + 2 := by
  have hb : MotifRecordSkip.timeBound n r + 2 ≤ 4 * L + 7 := by unfold MotifRecordSkip.timeBound; omega
  unfold MotifPrefixSkip.timeBound
  calc ci * (MotifRecordSkip.timeBound n r + 2) + (ci + 2) ≤ L * (4 * L + 7) + (L + 2) :=
      Nat.add_le_add (Nat.mul_le_mul hci hb) (Nat.add_le_add_right hci 2)
      _ = _ := by ring1

theorem hoareTime (m ci : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (hci : ci ≤ Q.coreCount) (before remaining emitted : List Bool) (hsplit : before ++ remaining = input)
    (R : (Fin (m + 22) → Tape) → Tape → Prop) :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        CurrentPins.Kept (m + 7) input work ∧ IsReg ci (work (core m)) ∧ R work out)
      (fun inp work out => Cursor (MotifPrefixData.before Q ci) (MotifPrefixData.remaining Q ci) emitted inp work out ∧
        (∀ j, Parked (work j)) ∧ CurrentPins.Kept (m + 7) input work ∧ IsReg ci (work (core m)) ∧ R work out)
      (timeBound input.length) := by
  have hs_ne : species m ≠ core m := by
    intro he; have hv := congrArg Fin.val he; change m + 17 = 13 at hv; omega
  have hr_ne : reactions m ≠ core m := by
    intro he; have hv := congrArg Fin.val he; change m + 18 = 13 at hv; omega
  have ha := MotifAccessCursor.hoareTime (m + 7) input Q hd before remaining emitted hsplit
    (fun work out => IsReg ci (work (core m)) ∧ R work out)
  have hp := MotifPrefixSkip.hoareTime (species m) (reactions m) (core m) hs_ne hr_ne
    ((MotifPrefixData.items Q).take ci) (MotifAccess.before Q) (MotifPrefixData.remaining Q ci) emitted
    (fun work out => (∀ j, Parked (work j)) ∧ CurrentPins.Kept (m + 7) input work ∧ R work out)
  have hfull := seqTM_hoareTime (MotifAccess.machine (m + 7)) (MotifPrefixSkip.machine (species m) (reactions m) (core m)) ha (by
    rintro inp work out ⟨hc, hs, hk, hcore, hR⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    have hcounts := CurrentPins.counts (m + 7) input Q hd work hk
    exact ⟨by simpa only [MotifPrefixData.tail_split Q ci, MotifPrefixData.wordPrefix] using hc,
      by simpa only [MotifPrefixData.prefix_count Q ci hci] using hcore, hcounts.1, hcounts.2, hs, hk, hR⟩) hp
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  have hb := prefix_runtime_bound input.length Q.speciesCount Q.reactionCount ci (by omega) (by omega)
  exact hfull.consequence (fun _ _ _ h => h) (by
    rintro inp work out ⟨hc, hcore, _, _, hs, hk, hR⟩
    exact ⟨by simpa only [MotifPrefixData.before, MotifPrefixData.wordPrefix] using hc,
      hs, hk, by simpa only [MotifPrefixData.prefix_count Q ci hci] using hcore, hR⟩) (by
        rw [MotifPrefixData.prefix_count Q ci hci]
        unfold timeBound MotifAccess.timeBound
        omega)

end JointThermoComplexity.Complexity.MotifIndexedAccess

#print axioms JointThermoComplexity.Complexity.MotifIndexedAccess.prefix_runtime_bound
#print axioms JointThermoComplexity.Complexity.MotifIndexedAccess.hoareTime
