module
public import proofs.JointThermoComplexity.Complexity.IndicatorVectorLoop
public import proofs.JointThermoComplexity.Complexity.BinaryBufferReset

set_option autoImplicit false
@[expose] public section

/-! Exact dense indicator vectors return a cleared reusable binary cell index. -/

namespace JointThermoComplexity.Complexity.ReusableIndicatorVector
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementRun
open IndicatorVectorLoop (Ports)
variable {w : ℕ}

def machine (d : Ports w) (k : ℕ) : TM (w + 1) :=
  seqTM (IndicatorVectorLoop.machine d k) (BinaryBufferReset.machine d.comparison.operand)

def bound (V T B k : ℕ) : ℕ := IndicatorVectorLoop.timeBound V T B k + 3 * T + 10

theorem hoareTime (d : Ports w) (k M start V T B : ℕ) (hT : start + V ≤ T) (hM : M.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : IndicatorVectorLoop.Stable d R) :
    (machine d k).HoareTime
      (fun inp work out => IndicatorVectorUnit.Pre d.comparison start M before input emitted R inp work out ∧ IsReg V (work d.fuel))
      (fun inp work out => IndicatorVectorUnit.Pre d.comparison 0 M before input
        (emitted ++ IndicatorVectorControl.words k M start V) R inp work out ∧ IsReg V (work d.fuel))
      (bound V T B k) := by
  let S : (Fin (w + 1) → Tape) → Prop := fun work => Register M (work d.comparison.constant) ∧
    (work d.comparison.flag).head = 1 ∧ IsReg V (work d.fuel) ∧ R work
  have hS : ∀ work next, (∀ j, j ≠ d.comparison.operand → next j = work j) → S work → S next := by
    rintro work next he ⟨hm, hf, hv, hr⟩
    exact ⟨by rw [he d.comparison.constant d.comparison.separate.operands.symm]; exact hm,
      by rw [he d.comparison.flag d.comparison.separate.flagLeft]; exact hf,
      by rw [he d.fuel d.fuel_idx]; exact hv,
      hR work next (fun j hj _ _ _ => he j hj) hr⟩
  have hl := IndicatorVectorLoop.hoareTime d k M start V T B hT hM before input emitted R hR
  have hr := BinaryBufferReset.hoareTime d.comparison.operand (start + V).bits before input
    (emitted ++ IndicatorVectorControl.words k M start V) S hS
  have hs := seqTM_hoareTime _ _ hl (by
    rintro inp work out ⟨⟨hc, hs, hi, hm, hh, hx⟩, hf⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨hc, hs, hi.1.2, hi.2, by rw [hi.1.1]; omega, hm, hh, hf, hx⟩) hr
  apply hs.consequence
  · intro inp work out hp
    simpa only [IndicatorVectorLoop.Inv, IndicatorVectorControl.words_zero, List.append_nil, Nat.add_zero] using hp
  · rintro inp work out ⟨hc, hs, hz, hm, hh, hf, hr⟩
    have hzero : Register 0 (work d.comparison.operand) :=
      ⟨by simpa only [Nat.zero_bits, List.replicate_zero] using CountTape.string_of_register hz, hz.cell0⟩
    exact ⟨⟨hc, hs, hzero, hm, hh, hr⟩, hf⟩
  · have hb := (BoundedUnaryControl.bits_le (start + V)).trans hT
    unfold bound
    omega

theorem code_hoareTime (d : Ports w) (k M start V T B : ℕ) (hT : start + V ≤ T) (hM : M.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : IndicatorVectorLoop.Stable d R) :
    (machine d k).HoareTime
      (fun inp work out => IndicatorVectorUnit.Pre d.comparison start M before input emitted R inp work out ∧ IsReg V (work d.fuel))
      (fun inp work out => IndicatorVectorUnit.Pre d.comparison 0 M before input
        (emitted ++ FiniteCodec.functionCode FiniteCodec.natural
          (fun j : Fin V => if start + j.val = M then k else 0)) R inp work out ∧ IsReg V (work d.fuel))
      (bound V T B k) := by
  simpa only [IndicatorVectorControl.words_code] using hoareTime d k M start V T B hT hM before input emitted R hR

theorem polynomial_bound (V T B k : ℕ) : bound V T B k =
    V * (26 * T + 24 * B + max (BitCodec.naturalCode k).length (BitCodec.naturalCode 0).length + 32) + 3 * T + 12 := by
  unfold bound
  rw [IndicatorVectorLoop.polynomial_timeBound]
  ring1

end JointThermoComplexity.Complexity.ReusableIndicatorVector

#print axioms JointThermoComplexity.Complexity.ReusableIndicatorVector.hoareTime
#print axioms JointThermoComplexity.Complexity.ReusableIndicatorVector.code_hoareTime
#print axioms JointThermoComplexity.Complexity.ReusableIndicatorVector.polynomial_bound
