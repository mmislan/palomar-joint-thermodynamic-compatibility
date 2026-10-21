module
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementFramed
public import proofs.JointThermoComplexity.Complexity.FixedOutput
public import Mathlib.Tactic.Linarith

set_option autoImplicit false
@[expose] public section

/-! Add a constant compiled into a finite program before input. Offset
templates use only constants2^d with d<=4; no input magnitude controls this loop. -/

namespace JointThermoComplexity.Complexity.BinaryConstantAdd
open _root_.Complexity _root_.Complexity.TM HeaderAt BinaryIncrementFramed
variable {w : ℕ}

def machine : ℕ → Fin w → TM w
  | 0, _ => emitBitsTM []
  | k + 1, idx => seqTM (machine k idx) (BinaryIncrementMachine.machine idx)

theorem bits_add (v k : ℕ) : (v + k).bits.length ≤ v.bits.length + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := BinaryIncrementControl.length_increment (v + k).bits
    rw [BinaryIncrementControl.increment_bits] at h
    simpa only [Nat.add_assoc] using h.trans (Nat.add_le_add_right ih 1)

theorem hoareTime (k : ℕ) (idx : Fin w) (v : ℕ) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) (hR : Stable idx R) :
    (machine k idx).HoareTime (Logical idx v before input emitted R)
      (Logical idx (v + k) before input emitted R) (k * (2 * v.bits.length + 2 * k + 5)) := by
  induction k with
  | zero =>
    have h := FixedOutput.hoareTime [] before input emitted
      (fun work => BinaryIncrementRun.Register v (work idx) ∧ R work)
    apply h.consequence (fun _ _ _ hp => hp)
    · intro inp work out hp
      simpa only [Logical, List.append_nil, Nat.add_zero] using hp
    · simp
  | succ k ih =>
    have hi := BinaryIncrementFramed.hoareTime idx (v + k) before input emitted R hR
    have hf := seqTM_hoareTime _ _ ih (by
      intro inp work out hp
      obtain ⟨hi, hw, ho⟩ := hp.1.phase
      rw [hi, hw, ho]
      exact hp) hi
    apply hf.consequence (fun _ _ _ hp => hp)
    · intro inp work out hp
      simpa only [Nat.add_assoc] using hp
    · have hbits := bits_add v k
      nlinarith

end JointThermoComplexity.Complexity.BinaryConstantAdd

#print axioms JointThermoComplexity.Complexity.BinaryConstantAdd.machine
#print axioms JointThermoComplexity.Complexity.BinaryConstantAdd.hoareTime
