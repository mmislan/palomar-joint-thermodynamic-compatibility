module
public import proofs.JointThermoComplexity.Complexity.BinaryCycleSuccessor
public import proofs.JointThermoComplexity.Complexity.DenseLiteralComplexCode

set_option autoImplicit false
@[expose] public section

/-! The actual binary successor agrees exactly with the original literal cycle and gain. -/

namespace JointThermoComplexity.Complexity.DenseCycleData
open _root_.Complexity _root_.Complexity.TM
variable {N : ℕ}

theorem next_eq (i : Fin (N + 2)) :
    BinaryCycleSuccessor.nextValue i.val (N + 1) = (finRotate (N + 2) i).val := by
  rw [coe_finRotate]
  simp only [BinaryCycleSuccessor.nextValue, Fin.ext_iff, Fin.val_last]

theorem gain_eq (i : Fin (N + 2)) :
    RationalLiteralNetwork.gain N i = if i.val = N + 1 then 2 else 1 := by
  simp only [RationalLiteralNetwork.gain, Fin.ext_iff, Fin.val_last]

theorem hoareTime (i : Fin (N + 2)) (u B : ℕ) (hi : i.val.bits.length ≤ B)
    (hend : (N + 1).bits.length ≤ B) (hu : u.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin 63 → Tape) → Prop) (hR : BinaryCycleSuccessor.Stable R) :
    BinaryCycleSuccessor.machine.HoareTime (BinaryCycleSuccessor.Pre i.val (N + 1) u before input emitted R)
      (BinaryCycleSuccessor.At i.val (N + 1) (finRotate (N + 2) i).val before input emitted R) (38 * B + 74) := by
  have hh := BinaryCycleSuccessor.hoareTime i.val (N + 1) u B hi hend hu before input emitted R hR
  simpa only [next_eq] using hh

theorem flag_gain (i : Fin (N + 2)) (R : (Fin 63 → Tape) → Prop) (work : Fin 64 → Tape)
    (hf : BinaryCycleSuccessor.Frame i.val (N + 1) R work) :
    (work 43).read = Γ.zero ↔ RationalLiteralNetwork.gain N i = 2 := by
  rw [hf.2.2.2.1]
  by_cases he : i.val = N + 1
  · simp [gain_eq, he, Γ.ofBool]
  · have hz : Γ.one ≠ Γ.zero := by decide
    simp [gain_eq, he, Γ.ofBool, hz]

end JointThermoComplexity.Complexity.DenseCycleData

#print axioms JointThermoComplexity.Complexity.DenseCycleData.hoareTime
#print axioms JointThermoComplexity.Complexity.DenseCycleData.flag_gain
