module
public import proofs.JointThermoComplexity.Complexity.NetworkEmitReady
public import proofs.JointThermoComplexity.Complexity.NetworkSeedPorts

set_option autoImplicit false
@[expose] public section

/-! Initialize the empty circuit invariant from bounded blank working registers and the retained offset. -/

namespace JointThermoComplexity.Complexity.NetworkSeed
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady ReactionPorts NetworkEmitReady

def machine (m : ℕ) : TM (m + 15) :=
  UnaryCopy.machine (NetworkSeedPorts.permutation m) (NetworkSeedPorts.sourceOld m) (scratchOld (m + 2))

theorem hoareTime (m L offset n : ℕ) (hoff : offset ≤ L) (before input emitted : List Bool)
    (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 2) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧ IsReg 0 (work (next (m + 2))) ∧
        IsReg offset (work (CountLayout.offset (m + 7))) ∧ Temps (m + 1) L work ∧
        IsReg 0 (work (previous (m + 1))) ∧ IsReg 0 (work (species (m + 1))) ∧
        IsReg 0 (work (saved m)) ∧ IsReg n (work (MonomialFuel.slot (m + 1))) ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready m L offset 0 n R work)
      (5 * L + 15) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work =>
    BinaryIncrementRun.Register 0 (work (scratch (m + 2))) ∧ Temps (m + 1) L work ∧
    IsReg 0 (work (previous (m + 1))) ∧ IsReg 0 (work (species (m + 1))) ∧
    IsReg 0 (work (saved m)) ∧ IsReg n (work (MonomialFuel.slot (m + 1))) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ CountSumAt.destination (NetworkSeedPorts.permutation m) →
      work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hz, ⟨a, p, ha, hp, har, hpr⟩, ho, hi, hk, hf, hr⟩
    rw [NetworkSeedPorts.destination] at hw
    exact ⟨by simpa only [hw _ (next_ne_scratch (m + 2)).symm] using hz,
      ⟨a, p, ha, hp, by simpa only [hw _ (next_ne_accumulator (m + 2)).symm] using har,
        by simpa only [hw _ (next_ne_power (m + 2)).symm] using hpr⟩,
      by simpa only [hw _ (previous_ne_next (m + 1))] using ho,
      by simpa only [hw _ (species_ne_next (m + 1))] using hi,
      by simpa only [hw _ (saved_ne_next m)] using hk,
      by simpa only [hw _ (MonomialFuel.slot_separate (m + 1)).next] using hf,
      hR work work' hw hr⟩
  have hc := UnaryCopy.hoareTime (NetworkSeedPorts.permutation m) (NetworkSeedPorts.sourceOld m)
    (scratchOld (m + 2)) 0 offset before input emitted P hP
  exact hc.consequence (by
    rintro inp work out ⟨hcur, hs, hz, hn, hoffset, ht, ho, hi, hk, hf, hr⟩
    refine ⟨hcur, hs, ?_, ?_, ?_, hz, ht, ho, hi, hk, hf, hr⟩
    · simpa only [NetworkSeedPorts.destination] using hn
    · simpa only [NetworkSeedPorts.source] using hoffset
    · rw [NetworkSeedPorts.zero]
      exact CountTape.register_of_string (by simpa only [Nat.zero_bits, List.replicate_zero] using hz.1) hz.2) (by
    rintro inp work out ⟨hcur, hs, hn, _, _, hz, ht, ho, hi, hk, hf, hr⟩
    exact ⟨hcur, hs, hz, by simpa only [NetworkSeedPorts.destination, Nat.add_zero] using hn,
      ht, ⟨0, by omega, ho⟩, ⟨0, by omega, hk⟩, ⟨0, by omega, hi⟩, hf, hr⟩) (by omega)

end JointThermoComplexity.Complexity.NetworkSeed

#print axioms JointThermoComplexity.Complexity.NetworkSeed.hoareTime
