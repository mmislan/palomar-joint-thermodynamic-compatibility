module
public import proofs.JointThermoComplexity.Complexity.CurrentStartPorts
public import proofs.JointThermoComplexity.Complexity.CurrentReady

set_option autoImplicit false
@[expose] public section

/-! Initialize the current-equation tally and source cursor even when the preceding reaction table was empty. -/

namespace JointThermoComplexity.Complexity.CurrentStart
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts CurrentPorts CurrentReady CurrentStartPorts

def rawMachine (m : ℕ) : TM (m + 15) := UnaryCopy.machine (Equiv.refl _) (offsetOld m) (scratchOld (m + 2))
def cursorMachine (m : ℕ) : TM (m + 15) :=
  UnaryCopy.machine (currentPermutation m) (speciesOld m) (scratchOld (m + 2))
def machine (m : ℕ) : TM (m + 15) := seqTM (rawMachine m) (cursorMachine m)

theorem hoareTime (m L offset n gate idx : ℕ) (hoff : offset ≤ L) (hn : n ≤ L) (hg : gate ≤ 3 * L) (hi : idx ≤ L)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ raw m → j ≠ species (m + 1) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧ IsReg gate (work (raw m)) ∧
        IsReg offset (work (CountLayout.offset (m + 7))) ∧ IsReg idx (work (species (m + 1))) ∧
        IsReg n (work (MonomialFuel.slot (m + 1))) ∧
        (∃ old, old ≤ 4 * L ∧ IsReg old (work (previous (m + 1)))) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready m L offset n n R work)
      (18 * L + 31) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work => BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
    IsReg idx (work (species (m + 1))) ∧ IsReg n (work (MonomialFuel.slot (m + 1))) ∧
    (∃ old, old ≤ 4 * L ∧ IsReg old (work (previous (m + 1)))) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ CountSumAt.destination (Equiv.refl (Fin (m + 15))) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hz, hi, hf, ⟨old, hold, hp⟩, hr⟩
    exact ⟨by simpa only [hw _ (raw_ne_scratch m).symm] using hz,
      by simpa only [hw _ (raw_ne_current m).symm] using hi,
      by simpa only [hw _ (raw_ne_speciesFuel m).symm] using hf,
      ⟨old, hold, by simpa only [hw _ (raw_ne_previous m).symm] using hp⟩,
      hR work work' (fun j hj _ => hw j hj) hr⟩
  have hraw := UnaryCopy.hoareTime (Equiv.refl (Fin (m + 15))) (offsetOld m) (scratchOld (m + 2)) gate offset
    before input emitted P hP
  let S : (Fin (m + 15) → Tape) → Prop := fun work => BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧
    IsReg offset (work (raw m)) ∧ (∃ old, old ≤ 4 * L ∧ IsReg old (work (previous (m + 1)))) ∧ R work
  have hS : ∀ work work', (∀ j, j ≠ CountSumAt.destination (currentPermutation m) → work' j = work j) → S work → S work' := by
    rintro work work' hw ⟨hz, hn, ⟨old, hold, hp⟩, hr⟩
    rw [current_destination] at hw
    exact ⟨by simpa only [hw _ (species_ne_scratch (m + 1)).symm] using hz,
      by simpa only [hw _ (raw_ne_current m)] using hn,
      ⟨old, hold, by simpa only [hw _ (previous_ne_species (m + 1))] using hp⟩,
      hR work work' (fun j _ hj => hw j hj) hr⟩
  have hcur := UnaryCopy.hoareTime (currentPermutation m) (speciesOld m) (scratchOld (m + 2)) idx n
    before input emitted S hS
  simp only [current_destination, current_source, current_zero] at hcur
  have hseq := seqTM_hoareTime (rawMachine m) (cursorMachine m) hraw (by
    rintro inp work out ⟨hc, hs, hn, _, hz, hbinary, hi, hf, hp, hr⟩
    obtain ⟨hip, hw, ho⟩ := hc.phase
    rw [hip, hw, ho]
    exact ⟨hc, hs, hi, hf, hz, hbinary, hn, hp, hr⟩) hcur
  exact hseq.consequence (by
    rintro inp work out ⟨hc, hs, hz, hg, ho, hi, hf, hp, hr⟩
    have hz' : IsReg 0 (work (scratch (m + 2))) :=
      CountTape.register_of_string (by simpa only [Nat.zero_bits, List.replicate_zero] using hz.1) hz.2
    exact ⟨hc, hs, hg, ho, hz', hz, hi, hf, hp, hr⟩)
    (fun _ _ _ ⟨hc, hs, hi, hf, _, hz, hn, hp, hr⟩ => ⟨hc, hs, hz, hn, hi, hp, hf, hr⟩) (by omega)

end JointThermoComplexity.Complexity.CurrentStart

#print axioms JointThermoComplexity.Complexity.CurrentStart.hoareTime
