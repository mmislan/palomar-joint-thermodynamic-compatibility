module
public import proofs.JointThermoComplexity.Complexity.BooleanCopy
public import proofs.JointThermoComplexity.Complexity.PayloadCopy

set_option autoImplicit false
@[expose] public section

/-! Exact signed-integer input copying with all work tapes preserved and no validity scratch. -/

namespace JointThermoComplexity.Complexity.LiteralCopy
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def machine : TM w := seqTM BooleanCopy.machine (PayloadFrame.machine w)

theorem signed_hoareTime (sign : Bool) (bits before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before ((sign :: BitCodec.encodeBits bits) ++ tail) emitted inp work out ∧ R work)
      (fun inp work out => Cursor (before ++ (sign :: BitCodec.encodeBits bits)) tail
        (emitted ++ (sign :: BitCodec.encodeBits bits)) inp work out ∧ R work)
      ((sign :: BitCodec.encodeBits bits).length + 3) := by
  have hs := BooleanCopy.hoareTime sign before (BitCodec.encodeBits bits ++ tail) emitted R
  have hp := PayloadCopy.hoareTime w bits (before ++ [sign]) tail (emitted ++ [sign]) R
  have hseq := seqTM_hoareTime BooleanCopy.machine (PayloadFrame.machine w) hs (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hp
  exact hseq.consequence (by
    rintro inp work out ⟨hc, hr⟩
    exact ⟨by simpa only [List.cons_append] using hc, hr⟩) (by
      rintro inp work out ⟨hc, hr⟩
      exact ⟨by simpa only [List.append_assoc, List.singleton_append] using hc, hr⟩)
    (by simp only [List.length_cons]; omega)

theorem integer_hoareTime (value : ℤ) (before tail emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before (BitCodec.integerCode value ++ tail) emitted inp work out ∧ R work)
      (fun inp work out => Cursor (before ++ BitCodec.integerCode value) tail
        (emitted ++ BitCodec.integerCode value) inp work out ∧ R work)
      ((BitCodec.integerCode value).length + 3) := by
  cases value with
  | ofNat n => exact signed_hoareTime false n.bits before tail emitted R
  | negSucc n => exact signed_hoareTime true (n + 1).bits before tail emitted R

end JointThermoComplexity.Complexity.LiteralCopy

#print axioms JointThermoComplexity.Complexity.LiteralCopy.integer_hoareTime
