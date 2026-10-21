module
public import proofs.JointThermoComplexity.Complexity.ReactionPorts
public import proofs.JointThermoComplexity.Complexity.MonomialReady
public import proofs.JointThermoComplexity.Complexity.UnaryCopy

set_option autoImplicit false
@[expose] public section

/-! Copy the completed reactant reference without changing the monomial or parser frame. -/

namespace JointThermoComplexity.Complexity.ReactionSave
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts MonomialReady ReactionPorts

def machine (m : ℕ) : TM (m + 15) :=
  UnaryCopy.machine (savedPermutation m) (copyPreviousOld m) (copyZeroOld m)

theorem hoareTime {n : ℕ} (m L offset idx old : ℕ) (s : MonomialCircuit.State n)
    (hold : old ≤ 4 * L) (hvalue : offset + s.accumulator.val ≤ 4 * L)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ saved m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready (m + 1) L offset s idx R work ∧
        IsReg old (work (saved m)))
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready (m + 1) L offset s idx R work ∧
        IsReg (offset + s.accumulator.val) (work (saved m))) (28 * L + 15) := by
  let P : (Fin (m + 15) → Tape) → Prop := fun work =>
    IsReg idx (work (species (m + 1))) ∧ Fixed (m + 1) L offset s R work
  have hP : ∀ work work', (∀ j, j ≠ CountSumAt.destination (savedPermutation m) → work' j = work j) →
      P work → P work' := by
    rintro work work' hw ⟨hi, hz, hn, hp, ⟨a, p, ha, hb, har, hpr⟩, hr⟩
    have hw' : ∀ j, j ≠ saved m → work' j = work j := by simpa only [saved_destination] using hw
    refine ⟨?_, ?_, ?_, ?_, ⟨a, p, ha, hb, ?_, ?_⟩, hR work work' hw' hr⟩
    · simpa only [hw' _ (saved_ne_species m).symm] using hi
    · simpa only [hw' _ (saved_ne_scratch m).symm] using hz
    · simpa only [hw' _ (saved_ne_next m).symm] using hn
    · simpa only [hw' _ (saved_ne_previous m).symm] using hp
    · simpa only [hw' _ (saved_ne_accumulator m).symm] using har
    · simpa only [hw' _ (saved_ne_power m).symm] using hpr
  have hc := UnaryCopy.hoareTime (savedPermutation m) (copyPreviousOld m) (copyZeroOld m)
    old (offset + s.accumulator.val) before input emitted P hP
  simp only [saved_destination, copy_previous, copy_zero, P] at hc
  exact hc.consequence (by
    rintro inp work out ⟨hcur, ⟨hs, hi, hz, hn, hp, ht, hr⟩, ho⟩
    have hz' : IsReg 0 (work (scratch (m + 2))) :=
      CountTape.register_of_string (by simpa only [Nat.zero_bits, List.replicate_zero] using hz.1) hz.2
    exact ⟨hcur, hs, ho, hp, hz', hi, hz, hn, hp, ht, hr⟩) (by
    rintro inp work out ⟨hcur, hs, ho, _, _, hi, hz, hn, hp, ht, hr⟩
    exact ⟨hcur, ⟨hs, hi, hz, hn, hp, ht, hr⟩, ho⟩) (by omega)

end JointThermoComplexity.Complexity.ReactionSave

#print axioms JointThermoComplexity.Complexity.ReactionSave.hoareTime
