module
public import proofs.JointThermoComplexity.Complexity.UnaryGateStore
public import proofs.JointThermoComplexity.Complexity.MonomialPorts
public import proofs.JointThermoComplexity.Complexity.PowerAddressFrame
public import proofs.JointThermoComplexity.Complexity.TemplateRuntime

set_option autoImplicit false
@[expose] public section

/-! The actual species-copy gate prepares the base reference for the exponent routine. -/

namespace JointThermoComplexity.Complexity.MonomialInput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts PowerAddressState MonomialPorts

def machine (m : ℕ) : TM (m + 14) :=
  UnaryGateStore.machine false (powerPermutation (m + 1)) (nextOld (m + 1))
    (scratchOld (m + 1)) (species m)

theorem hoareTime (m arity L : ℕ) (ha : arity ≤ 4 * L) (s : State)
    (hn : s.nextAddress < arity) (source : Fin arity) (hp : s.powerAddress ≤ 4 * L)
    (before input emitted : List Bool) (R : (Fin (m + 14) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next (m + 1) → j ≠ power (m + 1) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ PowerAddressFrame.Ready (m + 1) s R work ∧
        IsReg source.val (work (species m)))
      (fun inp work out => Cursor before input
        (emitted ++ (RealSyntax.Formula.eq (.var (⟨s.nextAddress, hn⟩ : Fin arity)) (.var source)).code) inp work out ∧
        PowerAddressFrame.Ready (m + 1) ⟨s.nextAddress + 1, s.accumulatorAddress, s.nextAddress⟩ R work ∧
        IsReg source.val (work (species m))) (64 * L ^ 2 + 132 * L + 69) := by
  let values : Fin (m + 14) → Fin arity := fun j => if j = next (m + 1) then ⟨s.nextAddress, hn⟩ else source
  have vnext : values (next (m + 1)) = ⟨s.nextAddress, hn⟩ := by simp only [values, ↓reduceIte]
  have vspecies : values (species m) = source := by simp only [values, species_ne_next, ↓reduceIte]
  have ht : GateStore.next (powerPermutation (m + 1)) (nextOld (m + 1)) ≠
      GateStore.scratch (powerPermutation (m + 1)) (scratchOld (m + 1)) := by
    simpa only [power_next, power_scratch] using next_ne_scratch (m + 1)
  have hf : species m ≠ GateStore.scratch (powerPermutation (m + 1)) (scratchOld (m + 1)) := by
    simpa only [power_scratch] using species_ne_scratch m
  let P : (Fin (m + 14) → Tape) → Prop := fun work =>
    IsReg s.accumulatorAddress (work (accumulator (m + 1))) ∧ IsReg source.val (work (species m)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ GateStore.next (powerPermutation (m + 1)) (nextOld (m + 1)) →
      j ≠ CountSumAt.destination (powerPermutation (m + 1)) → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨ha, hs, hr⟩
    have hw' : ∀ j, j ≠ next (m + 1) → j ≠ power (m + 1) → work' j = work j := by
      simpa only [power_next, power_destination] using hw
    exact ⟨by simpa only [hw' _ (next_ne_accumulator (m + 1)).symm (accumulator_ne_power (m + 1))] using ha,
      by simpa only [hw' _ (species_ne_next m) (species_ne_power m)] using hs, hR work work' hw' hr⟩
  have h := UnaryGateStore.hoareTime false (powerPermutation (m + 1)) (nextOld (m + 1))
    (scratchOld (m + 1)) (species m) ht hf values s.powerAddress before input emitted P hP
  simp only [power_next, power_scratch, power_destination, vnext, vspecies, P,
    UnaryGateOutput.formula, Bool.false_eq_true, ↓reduceIte] at h
  have hb := TemplateRuntime.unary_bound (fun j => (values j).val) (next (m + 1)) (species m) L
    (by rw [vnext]; omega) (by rw [vspecies]; exact source.isLt.le.trans ha)
  apply h.consequence
  · rintro inp work out ⟨hc, ⟨hs, hz, hn, ha, hp, hr⟩, hi⟩
    exact ⟨hc, hs, hz, hn, hi, hp, ha, hi, hr⟩
  · rintro inp work out ⟨hc, hs, hz, hn, hp, ha, hi, hr⟩
    exact ⟨hc, ⟨hs, hz, hn, ha, hp, hr⟩, hi⟩
  · change UnaryGateOutput.timeBound (fun j : Fin (m + 14) => (values j).val)
      (next (m + 1)) (species m) + 2 * s.powerAddress + 7 * s.nextAddress + 23 ≤ _
    omega

end JointThermoComplexity.Complexity.MonomialInput

#print axioms JointThermoComplexity.Complexity.MonomialInput.hoareTime
