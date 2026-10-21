module
public import proofs.JointThermoComplexity.Complexity.PowerBitDispatch
public import proofs.JointThermoComplexity.Complexity.ReadBitFlag

set_option autoImplicit false
@[expose] public section

/-! Read the actual payload bit and execute its gate block with a proved polynomial bound. -/

namespace JointThermoComplexity.Complexity.PowerBitStep
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun PowerPorts PowerBitState

variable {arity : ℕ}

def machine (m : ℕ) : TM (m + 13) :=
  seqTM (ReadBitFlag.machine (PowerBitState.flag m)) (PowerBitDispatch.machine m)

def timeBound (L : ℕ) : ℕ := bound L + 2

theorem timeBound_eq (L : ℕ) : timeBound L = 192 * L ^ 2 + 360 * L + 180 := by
  unfold timeBound bound
  omega

theorem hoareTime (m : ℕ) (values : Fin (m + 13) → Fin arity) (bit : Bool)
    (room : bit = true → (values (next m)).val + 1 < arity) (L : ℕ) (ha : arity ≤ 4 * L)
    (before tail emitted : List Bool) (R : (Fin (m + 13) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next m → j ≠ accumulator m → j ≠ power m → j ≠ PowerBitState.flag m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before (bit :: tail) emitted inp work out ∧ Ready m values R work)
      (fun inp work out => Cursor (before ++ [bit]) tail (emitted ++ word m values bit room) inp work out ∧ After m values bit R work)
      (timeBound L) := by
  let P : (Fin (m + 13) → Tape) → Prop := fun work => Register 0 (work (scratch m)) ∧
    IsReg (values (next m)).val (work (next m)) ∧ IsReg (values (accumulator m)).val (work (accumulator m)) ∧
    IsReg (values (power m)).val (work (power m)) ∧ R work
  have hP : ∀ work work', (∀ j, j ≠ PowerBitState.flag m → work' j = work j) → P work → P work' := by
    rintro work work' hw ⟨hz, hn, ha, hp, hr⟩
    exact ⟨by simpa only [hw _ (scratch_ne_flag m)] using hz,
      by simpa only [hw _ (next_ne_flag m)] using hn,
      by simpa only [hw _ (accumulator_ne_flag m)] using ha,
      by simpa only [hw _ (power_ne_flag m)] using hp,
      hR work work' (fun j _ _ _ hj => hw j hj) hr⟩
  have hread := ReadBitFlag.hoareTime (PowerBitState.flag m) bit before tail emitted P hP
  have hdispatch := PowerBitDispatch.hoareTime m values bit room L ha (before ++ [bit]) tail emitted R
    (fun work work' hw hr => hR work work' (fun j hn ha hp _ => hw j hn ha hp) hr)
  have hseq := seqTM_hoareTime (ReadBitFlag.machine (PowerBitState.flag m)) (PowerBitDispatch.machine m) hread (by
    rintro inp work out ⟨hc, hs, hf, hz, hn, ha, hp, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨⟨hc, hs, hz, hn, ha, hp, hr⟩, hf⟩) hdispatch
  exact hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => h) (by unfold timeBound; omega)

end JointThermoComplexity.Complexity.PowerBitStep

#print axioms JointThermoComplexity.Complexity.PowerBitStep.hoareTime
