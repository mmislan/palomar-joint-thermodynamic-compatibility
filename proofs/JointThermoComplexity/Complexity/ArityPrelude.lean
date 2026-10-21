module
public import proofs.JointThermoComplexity.Complexity.CountLayout
public import proofs.JointThermoComplexity.Complexity.ArityValue

set_option autoImplicit false
@[expose] public section

/-! Compute the auxiliary offset and total binder count in two reserved runtime registers. -/

namespace JointThermoComplexity.Complexity.ArityPrelude
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt CountLayout

def offsetMachine (m : ℕ) : TM (m + 8) := CountSumAt.machine (offsetPermutation m)
  (NetworkParser.count (m + 2) 0) (NetworkParser.count (m + 2) 1)

def binderMachine (m : ℕ) : TM (m + 8) := CountSumAt.machine (binderPermutation m) (binderOld m) (offsetOld m)

def machine (m : ℕ) : TM (m + 8) := seqTM (offsetMachine m) (binderMachine m)

theorem hoareTime (m : ℕ) (input before remaining emitted : List Bool) (R : (Fin (m + 8) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ offset m → j ≠ binder m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg (GateCountValue.count input) (work (raw m)) ∧ IsReg 0 (work (offset m)) ∧ IsReg 0 (work (binder m)) ∧
        ParserRegisters.Kept (m + 2) input (CountAppend.oldWork work) ∧ R work)
      (fun inp work out => Cursor before remaining emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        IsReg (GateCountValue.count input) (work (raw m)) ∧ IsReg (ArityValue.offset input) (work (offset m)) ∧
        IsReg (ArityValue.arity input) (work (binder m)) ∧ ParserRegisters.Kept (m + 2) input (CountAppend.oldWork work) ∧ R work)
      (25 * input.length + 19) := by
  rintro inp work out ⟨hc, hs, hg, hz, hb, hk, hr⟩
  let R₀ : (Fin (m + 8) → Tape) → Prop := fun work =>
    IsReg (GateCountValue.count input) (work (raw m)) ∧ IsReg 0 (work (binder m)) ∧
    ParserRegisters.Kept (m + 2) input (CountAppend.oldWork work) ∧ R work
  have hR₀ : ∀ work work', (∀ j, j ≠ CountSumAt.destination (offsetPermutation m) → work' j = work j) → R₀ work → R₀ work' := by
    rintro work work' hw ⟨hg, hb, hk, hr⟩
    have hwo : ∀ j, j ≠ offset m → work' j = work j := by simpa only [offset_destination] using hw
    exact ⟨by simpa only [hwo _ (raw_ne_offset m)] using hg,
      by simpa only [hwo _ (offset_ne_binder m).symm] using hb,
      kept_frame m input (offset m) (by change (0 : ℕ) < 2; decide) work work' hwo hk,
      hR work work' (fun j hj _ => hwo j hj) hr⟩
  have hsp : IsReg (DimensionHeaders.species input) (work (RoutedNetworkParser.count (m + 2) 0)) := hk.2.2.1
  have hre : IsReg (DimensionHeaders.reactions input) (work (RoutedNetworkParser.count (m + 2) 1)) := hk.2.2.2.1
  obtain ⟨c, tc, htc, hcreach, hchalt, _hca, _hcb, hcp, hccur, hcsafe, hcR⟩ :=
    CountSumAt.hoareTime (offsetPermutation m) (NetworkParser.count (m + 2) 0) (NetworkParser.count (m + 2) 1)
      (DimensionHeaders.species input) (DimensionHeaders.reactions input) before remaining emitted R₀ hR₀
      inp work out ⟨by simpa only [offset_source] using hsp, by simpa only [offset_source] using hre,
        by simpa only [offset_destination] using hz, hc, hs, hg, hb, hk, hr⟩
  have hco : IsReg (ArityValue.offset input) (c.work (offset m)) := by
    simpa only [offset_destination, ArityValue.offset] using hcp
  let R₁ : (Fin (m + 8) → Tape) → Prop := fun work =>
    IsReg (GateCountValue.count input) (work (raw m)) ∧ IsReg (ArityValue.offset input) (work (offset m)) ∧
    ParserRegisters.Kept (m + 2) input (CountAppend.oldWork work) ∧ R work
  have hR₁ : ∀ work work', (∀ j, j ≠ CountSumAt.destination (binderPermutation m) → work' j = work j) → R₁ work → R₁ work' := by
    rintro work work' hw ⟨hg, ho, hk, hr⟩
    have hwb : ∀ j, j ≠ binder m → work' j = work j := by simpa only [binder_destination] using hw
    exact ⟨by simpa only [hwb _ (raw_ne_binder m)] using hg,
      by simpa only [hwb _ (offset_ne_binder m)] using ho,
      kept_frame m input (binder m) (by change (1 : ℕ) < 2; decide) work work' hwb hk,
      hR work work' (fun j _ hj => hwb j hj) hr⟩
  obtain ⟨e, te, hte, hereach, hehalt, _hea, _heb, hep, hecur, hesafe, heR⟩ :=
    CountSumAt.hoareTime (binderPermutation m) (binderOld m) (offsetOld m)
      (GateCountValue.count input) (ArityValue.offset input) before remaining emitted R₁ hR₁
      c.input c.work c.output ⟨by simpa only [binder_gate_source] using hcR.1,
        by simpa only [binder_offset_source] using hco, by simpa only [binder_destination] using hcR.2.1,
        hccur, hcsafe, hcR.1, hco, hcR.2.2.1, hcR.2.2.2⟩
  have hv : GateCountValue.count input + ArityValue.offset input = ArityValue.arity input := by
    unfold ArityValue.arity
    omega
  have heBinder : IsReg (ArityValue.arity input) (e.work (binder m)) := by
    simpa only [binder_destination, hv] using hep
  obtain ⟨hi, hw, ho⟩ := hccur.phase
  have hrr : (binderMachine m).reachesIn te
      ⟨(binderMachine m).qstart, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ e := by
    simpa only [binderMachine, hi, hw, ho] using hereach
  have hreach := seqTM_reachesIn_of_reachesIn (offsetMachine m) (binderMachine m) hcreach hchalt hrr
  have htco : tc ≤ 5 * ArityValue.offset input + 9 := by simpa only [ArityValue.offset] using htc
  have hbound : tc + 1 + te ≤ 25 * input.length + 19 := by
    have hoff := ArityValue.offset_bound input
    have hgate := GateCountValue.bound input
    omega
  exact ⟨phase2Wrap (offsetMachine m) (binderMachine m) e, tc + 1 + te, hbound, hreach,
    (phase2Wrap_halted_iff _ _ e).mpr hehalt, hecur, hesafe, heR.1, heR.2.1, heBinder, heR.2.2.1, heR.2.2.2⟩

end JointThermoComplexity.Complexity.ArityPrelude

#print axioms JointThermoComplexity.Complexity.ArityPrelude.hoareTime
