module
public import proofs.JointThermoComplexity.Complexity.MonomialAdvance

set_option autoImplicit false
@[expose] public section

/-! The monomial-loop invariant records exact circuit/result addresses and bounded temporary registers. -/

namespace JointThermoComplexity.Complexity.MonomialReady
open _root_.Complexity
open _root_.Complexity.TM
open PowerPorts MonomialPorts BinaryIncrementRun

def Temps (m L : ℕ) (work : Fin (m + 14) → Tape) : Prop :=
  ∃ a p : ℕ, a ≤ 4 * L ∧ p ≤ 4 * L ∧
    IsReg a (work (accumulator (m + 1))) ∧ IsReg p (work (power (m + 1)))

def Fixed {n : ℕ} (m L offset : ℕ) (s : MonomialCircuit.State n)
    (R : (Fin (m + 14) → Tape) → Prop) (work : Fin (m + 14) → Tape) : Prop :=
  Register 0 (work (scratch (m + 1))) ∧ IsReg (offset + s.size) (work (next (m + 1))) ∧
    IsReg (offset + s.accumulator.val) (work (previous m)) ∧ Temps m L work ∧ R work

def Ready {n : ℕ} (m L offset : ℕ) (s : MonomialCircuit.State n) (idx : ℕ)
    (R : (Fin (m + 14) → Tape) → Prop) (work : Fin (m + 14) → Tape) : Prop :=
  (∀ j, Parked (work j)) ∧ IsReg idx (work (species m)) ∧ Fixed m L offset s R work

theorem fixed_species {n : ℕ} (m L offset : ℕ) (s : MonomialCircuit.State n)
    (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ species m → work' j = work j) → R work → R work') :
    ∀ work work', (∀ j, j ≠ species m → work' j = work j) → Fixed m L offset s R work → Fixed m L offset s R work' := by
  rintro work work' hw ⟨hz, hn, hp, ⟨a, p, ha, hb, har, hpr⟩, hr⟩
  exact ⟨by simpa only [hw _ (species_ne_scratch m).symm] using hz,
    by simpa only [hw _ (species_ne_next m).symm] using hn,
    by simpa only [hw _ (previous_ne_species m)] using hp,
    ⟨a, p, ha, hb, by simpa only [hw _ (species_ne_accumulator m).symm] using har,
      by simpa only [hw _ (species_ne_power m).symm] using hpr⟩, hR work work' hw hr⟩

end JointThermoComplexity.Complexity.MonomialReady

#print axioms JointThermoComplexity.Complexity.MonomialReady.fixed_species
