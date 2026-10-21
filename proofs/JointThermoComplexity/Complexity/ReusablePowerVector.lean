module
public import proofs.JointThermoComplexity.Complexity.PowerVectorLoop
public import proofs.JointThermoComplexity.Complexity.BinaryBufferReset

set_option autoImplicit false
@[expose] public section

/-! Exact binary-reference power vectors return a zeroed reusable binary cell index. -/

namespace JointThermoComplexity.Complexity.ReusablePowerVector
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open SmallCoefficientMatch (Ports)
open PowerVectorLoop (Layout)
variable {w : ℕ}

def machine (d : Layout w) (weights : Ports w → ℕ) : TM (w + 1) :=
  seqTM (PowerVectorLoop.machine d weights) (BinaryBufferReset.machine d.cell.idx)

def bound (V T B : ℕ) : ℕ := PowerVectorLoop.timeBound V T B + 3 * T + 10

theorem hoareTime (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ)
    (start V T B : ℕ) (hT : start + V ≤ T)
    (hbits : ∀ p ∈ d.cell.comparisons, (values p.constant).bits.length ≤ B)
    (hcount : d.cell.comparisons.length ≤ 4)
    (hweight : PowerCellWord.weight (PowerCellEmit.items d.cell.comparisons weights) ≤ 4)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : PowerVectorLoop.Stable d R) :
    (machine d weights).HoareTime
      (fun inp work out => PowerVectorUnit.Pre d.cell values start before input emitted R inp work out ∧ IsReg V (work d.fuel))
      (fun inp work out => PowerVectorUnit.Pre d.cell values 0 before input
        (emitted ++ PowerVectorControl.words d.cell weights values start V) R inp work out ∧ IsReg V (work d.fuel))
      (bound V T B) := by
  let S : (Fin (w + 1) → Tape) → Prop := fun work => PowerVectorUnit.Refs d.cell values work ∧ IsReg V (work d.fuel) ∧ R work
  have hS : ∀ work next, (∀ j, j ≠ d.cell.idx → next j = work j) → S work → S next := by
    rintro work next he ⟨hr, hf, hx⟩
    refine ⟨?_, ?_, hR work next (fun j hj _ _ => he j hj) hx⟩
    · intro p hp
      rw [he p.constant (PowerVectorControl.constant_ne_idx d.cell p hp), he p.flag (PowerVectorControl.flag_ne_idx d.cell p hp)]
      exact hr p hp
    · rw [he d.fuel d.fuel_idx]; exact hf
  have hl := PowerVectorLoop.hoareTime d weights values start V T B hT hbits hcount hweight before input emitted R hR
  have hr := BinaryBufferReset.hoareTime d.cell.idx (start + V).bits before input
    (emitted ++ PowerVectorControl.words d.cell weights values start V) S hS
  have hs := seqTM_hoareTime _ _ hl (by
    rintro inp work out ⟨⟨hc, hs, hi, hr, hx⟩, hf⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨hc, hs, hi.1.2, hi.2, by rw [hi.1.1]; omega, hr, hf, hx⟩) hr
  apply hs.consequence
  · intro inp work out hp
    simpa only [PowerVectorLoop.Inv, PowerVectorControl.words_zero, List.append_nil, Nat.add_zero] using hp
  · rintro inp work out ⟨hc, hs, hz, hr, hf, hx⟩
    have hzero : Register 0 (work d.cell.idx) :=
      ⟨by simpa only [Nat.zero_bits, List.replicate_zero] using CountTape.string_of_register hz, hz.cell0⟩
    exact ⟨⟨hc, hs, hzero, hr, hx⟩, hf⟩
  · have hb := (BoundedUnaryControl.bits_le (start + V)).trans hT
    unfold bound
    omega

theorem code_hoareTime (d : Layout w) (weights : Ports w → ℕ) (values : Fin (w + 1) → ℕ)
    (start V T B : ℕ) (hT : start + V ≤ T)
    (hbits : ∀ p ∈ d.cell.comparisons, (values p.constant).bits.length ≤ B)
    (hcount : d.cell.comparisons.length ≤ 4)
    (hweight : PowerCellWord.weight (PowerCellEmit.items d.cell.comparisons weights) ≤ 4)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : PowerVectorLoop.Stable d R) :
    (machine d weights).HoareTime
      (fun inp work out => PowerVectorUnit.Pre d.cell values start before input emitted R inp work out ∧ IsReg V (work d.fuel))
      (fun inp work out => PowerVectorUnit.Pre d.cell values 0 before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (fun j : Fin V => PowerVectorControl.cell d.cell weights values (start + j.val))) R inp work out ∧ IsReg V (work d.fuel))
      (bound V T B) := by
  simpa only [PowerVectorControl.words_code] using hoareTime d weights values start V T B hT hbits hcount hweight before input emitted R hR

theorem polynomial_bound (V T B : ℕ) : bound V T B = V * (98 * T + 96 * B + 114) + 3 * T + 12 := by
  unfold bound
  rw [PowerVectorLoop.polynomial_timeBound]
  ring1

end JointThermoComplexity.Complexity.ReusablePowerVector

#print axioms JointThermoComplexity.Complexity.ReusablePowerVector.hoareTime
#print axioms JointThermoComplexity.Complexity.ReusablePowerVector.code_hoareTime
#print axioms JointThermoComplexity.Complexity.ReusablePowerVector.polynomial_bound
