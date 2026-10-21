module
public import proofs.JointThermoComplexity.Complexity.MonomialPorts
public import proofs.JointThermoComplexity.Complexity.PowerAddressFrame
public import proofs.JointThermoComplexity.Complexity.GateStoreRuntime

set_option autoImplicit false
@[expose] public section

/-! Multiply the previous monomial by its computed power, then store the fresh result. -/

namespace JointThermoComplexity.Complexity.MonomialProduct
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts PowerAddressState MonomialPorts

def machine (m : ℕ) : TM (m + 14) :=
  GateStore.machine (resultPermutation m) (nextOld (m + 1)) (scratchOld (m + 1))
    (previous m) (accumulator (m + 1))

theorem hoareTime (m arity L : ℕ) (ha : arity ≤ 4 * L) (s : State)
    (hn : s.nextAddress < arity) (hac : s.accumulatorAddress < arity) (old : Fin arity)
    (before input emitted : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ previous m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ PowerAddressFrame.Ready (m + 1) s R work ∧
        IsReg old.val (work (previous m)))
      (fun inp work out => Cursor before input (emitted ++
        BinaryPowerCode.multiply (⟨s.nextAddress, hn⟩ : Fin arity) old ⟨s.accumulatorAddress, hac⟩) inp work out ∧
        PowerAddressFrame.Ready (m + 1) ⟨s.nextAddress + 1, s.accumulatorAddress, s.powerAddress⟩ R work ∧
        IsReg s.nextAddress (work (previous m))) (96 * L ^ 2 + 180 * L + 88) := by
  let values : Fin (m + 14) → Fin arity := fun j =>
    if j = next (m + 1) then ⟨s.nextAddress, hn⟩ else if j = previous m then old else ⟨s.accumulatorAddress, hac⟩
  have vn : values (next (m + 1)) = ⟨s.nextAddress, hn⟩ := by simp only [values, ↓reduceIte]
  have vp : values (previous m) = old := by simp only [values, previous_ne_next, ↓reduceIte]
  have va : values (accumulator (m + 1)) = ⟨s.accumulatorAddress, hac⟩ := by
    simp only [values, (next_ne_accumulator (m + 1)).symm, (previous_ne_accumulator m).symm, ↓reduceIte]
  let P : (Fin (m + 14) → Tape) → Prop := fun work =>
    IsReg s.accumulatorAddress (work (accumulator (m + 1))) ∧ IsReg s.powerAddress (work (power (m + 1))) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ previous m → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hac, hp, hr⟩
    exact ⟨by simpa only [hw _ (next_ne_accumulator (m + 1)).symm (previous_ne_accumulator m).symm] using hac,
      by simpa only [hw _ (next_ne_power (m + 1)).symm (previous_ne_power m).symm] using hp,
      hR work work' hw hr⟩
  have h := PowerGateStore.hoareTime (m + 1) (resultPermutation m) (nextOld (m + 1)) (scratchOld (m + 1))
    (previous m) (previous m) (accumulator (m + 1)) (result_next m) (result_scratch m) (result_destination m)
    (previous_ne_scratch m) (accumulator_ne_scratch (m + 1)) values old.val before input emitted P hP
  simp only [vn, vp, va, P, BinaryGateOutput.formula, ↓reduceIte] at h
  have hv : ∀ j, (values j).val ≤ 4 * L := fun j => (values j).isLt.le.trans ha
  have hb := GateStoreRuntime.bound (fun j => (values j).val) old.val (next (m + 1)) (previous m)
    (accumulator (m + 1)) L (hv _) (hv _) (hv _) (old.isLt.le.trans ha)
  apply h.consequence
  · rintro inp work out ⟨hc, ⟨hs, hz, hn, hac, hp, hr⟩, ho⟩
    exact ⟨hc, hs, hz, hn, ho, hac, ho, hac, hp, hr⟩
  · rintro inp work out ⟨hc, hs, hz, hn, ho, hac, hp, hr⟩
    exact ⟨hc, ⟨hs, hz, hn, hac, hp, hr⟩, ho⟩
  · exact hb

end JointThermoComplexity.Complexity.MonomialProduct

#print axioms JointThermoComplexity.Complexity.MonomialProduct.hoareTime
