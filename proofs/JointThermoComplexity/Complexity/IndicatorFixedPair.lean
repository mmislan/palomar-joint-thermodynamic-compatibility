module
public import proofs.JointThermoComplexity.Complexity.IndicatorVectorControl
public import proofs.JointThermoComplexity.Complexity.IndicatorVectorUnit
public import proofs.JointThermoComplexity.Complexity.BinaryBufferReset

set_option autoImplicit false
@[expose] public section

/-! Two shared-species indicator cells need no additional unary loop counter. -/

namespace JointThermoComplexity.Complexity.IndicatorFixedPair
open _root_.Complexity _root_.Complexity.TM BinaryIncrementRun
open HeaderAt (Cursor)
open SmallCoefficientMatch (Ports)
variable {w : ℕ}

def pair (p : Ports w) (k : ℕ) : TM (w + 1) := seqTM (IndicatorVectorUnit.machine p k) (IndicatorVectorUnit.machine p k)
def machine (p : Ports w) (k : ℕ) : TM (w + 1) := seqTM (pair p k) (BinaryBufferReset.machine p.operand)
def bound (B k : ℕ) : ℕ := 2 * IndicatorVectorUnit.bound 2 B k + 17

theorem words_two (k M : ℕ) : IndicatorVectorControl.words k M 0 2 =
    BinaryEqualityEmit.word k 0 M ++ BinaryEqualityEmit.word k 1 M := by
  rw [IndicatorVectorControl.words_succ, IndicatorVectorControl.words_succ, IndicatorVectorControl.words_zero]
  simp only [Nat.zero_add, List.nil_append]

theorem hoareTime (p : Ports w) (k M B : ℕ) (hM : M.bits.length ≤ B) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) (hR : IndicatorVectorUnit.Stable p R) :
    (machine p k).HoareTime (IndicatorVectorUnit.Pre p 0 M before input emitted R)
      (IndicatorVectorUnit.Pre p 0 M before input (emitted ++ IndicatorVectorControl.words k M 0 2) R)
      (bound B k) := by
  have h0 := IndicatorVectorUnit.hoareTime p k 0 M 2 B (by decide) hM before input emitted R hR
  have h1 := IndicatorVectorUnit.hoareTime p k 1 M 2 B (by decide) hM before input
    (emitted ++ BinaryEqualityEmit.word k 0 M) R hR
  have hp := seqTM_hoareTime _ _ h0 (by
    rintro inp work out hx
    obtain ⟨hi, hw, ho⟩ := hx.1.phase
    rw [hi, hw, ho]
    exact hx) h1
  let S : (Fin (w + 1) → Tape) → Prop := fun work => Register M (work p.constant) ∧ (work p.flag).head = 1 ∧ R work
  have hS : ∀ work next, (∀ j, j ≠ p.operand → next j = work j) → S work → S next := by
    rintro work next he ⟨hm, hf, hr⟩
    exact ⟨by rw [he p.constant p.separate.operands.symm]; exact hm,
      by rw [he p.flag p.separate.flagLeft]; exact hf, hR work next (fun j hj _ _ => he j hj) hr⟩
  have hr := BinaryBufferReset.hoareTime p.operand (2 : ℕ).bits before input
    ((emitted ++ BinaryEqualityEmit.word k 0 M) ++ BinaryEqualityEmit.word k 1 M) S hS
  have hs := seqTM_hoareTime _ _ hp (by
    rintro inp work out ⟨hc, hs, hi, hm, hf, hx⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨hc, hs, hi.1.2, hi.2, by rw [hi.1.1]; omega, hm, hf, hx⟩) hr
  apply hs.consequence
  · exact fun _ _ _ hx => hx
  · rintro inp work out ⟨hc, hs, hz, hm, hf, hr⟩
    have hzero : Register 0 (work p.operand) :=
      ⟨by simpa only [Nat.zero_bits, List.replicate_zero] using CountTape.string_of_register hz, hz.cell0⟩
    exact ⟨by simpa only [words_two, List.append_assoc] using hc, hs, hzero, hm, hf, hr⟩
  · have hb : (2 : ℕ).bits.length = 2 := by decide
    unfold bound
    rw [hb]
    omega

end JointThermoComplexity.Complexity.IndicatorFixedPair

#print axioms JointThermoComplexity.Complexity.IndicatorFixedPair.hoareTime
