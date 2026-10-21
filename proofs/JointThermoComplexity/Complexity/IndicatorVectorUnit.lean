module
public import proofs.JointThermoComplexity.Complexity.BinaryEqualityEmit
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementFramed
public import proofs.JointThermoComplexity.Complexity.BoundedUnaryControl

set_option autoImplicit false
@[expose] public section

/-! One exact dense indicator cell followed by a retained binary index increment. -/

namespace JointThermoComplexity.Complexity.IndicatorVectorUnit
open _root_.Complexity _root_.Complexity.TM BinaryIncrementRun
open HeaderAt (Cursor)
open SmallCoefficientMatch (Ports)
variable {w : ℕ}

def Stable (p : Ports w) (R : (Fin (w + 1) → Tape) → Prop) : Prop :=
  ∀ work next, (∀ j, j ≠ p.operand → j ≠ p.constant → j ≠ p.flag → next j = work j) → R work → R next

def Fields (p : Ports w) (i M : ℕ) (R : (Fin (w + 1) → Tape) → Prop) (work : Fin (w + 1) → Tape) : Prop :=
  Register i (work p.operand) ∧ Register M (work p.constant) ∧ (work p.flag).head = 1 ∧ R work

def Pre (p : Ports w) (i M : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Fields p i M R work

def machine (p : Ports w) (k : ℕ) : TM (w + 1) :=
  seqTM (BinaryEqualityEmit.machine p k) (BinaryIncrementMachine.machine p.operand)

def bound (T B k : ℕ) : ℕ :=
  26 * T + 24 * B + max (BitCodec.naturalCode k).length (BitCodec.naturalCode 0).length + 29

theorem hoareTime (p : Ports w) (k i M T B : ℕ) (hi : i ≤ T) (hM : M.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : Stable p R) :
    (machine p k).HoareTime (Pre p i M before input emitted R)
      (Pre p (i + 1) M before input (emitted ++ BinaryEqualityEmit.word k i M) R) (bound T B k) := by
  have hRi : SmallCoefficientMatch.Stable p R := fun work next he => hR work next (fun j _ hc hf => he j hc hf)
  have hiBits : i.bits.length ≤ T + B := by have hh := (BoundedUnaryControl.bits_le i).trans hi; omega
  have hMBits : M.bits.length ≤ T + B := by omega
  have he := BinaryEqualityEmit.hoareTime p k i M (T + B) hiBits hMBits before input emitted R hRi
  let S : (Fin (w + 1) → Tape) → Prop := fun work =>
    Register M (work p.constant) ∧ (work p.flag).head = 1 ∧ R work
  have hS : BinaryIncrementFramed.Stable p.operand S := by
    rintro work next he ⟨hm, hf, hr⟩
    exact ⟨by rw [he p.constant p.separate.operands.symm]; exact hm,
      by rw [he p.flag p.separate.flagLeft]; exact hf,
      hR work next (fun j hj _ _ => he j hj) hr⟩
  have hi' := BinaryIncrementFramed.bounded_hoareTime p.operand i T ((BoundedUnaryControl.bits_le i).trans hi)
    before input (emitted ++ BinaryEqualityEmit.word k i M) S hS
  have hh := seqTM_hoareTime _ _ he (by
    rintro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.phase
    rw [hi, hw, ho]
    exact hp) hi'
  exact hh.mono_bound (by unfold bound BinaryEqualityEmit.bound; omega)

end JointThermoComplexity.Complexity.IndicatorVectorUnit

#print axioms JointThermoComplexity.Complexity.IndicatorVectorUnit.hoareTime
