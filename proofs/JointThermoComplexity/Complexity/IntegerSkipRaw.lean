module
public import proofs.JointThermoComplexity.Complexity.InputBitSkip

set_option autoImplicit false
@[expose] public section

/-! Total read-only signed-field traversal with exact cursor and whole work/output preservation. -/

namespace JointThermoComplexity.Complexity.IntegerSkipRaw
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def machine : TM w := seqTM InputBitSkip.machine NaturalSkip.machine

theorem copied_eq (input : List Bool) :
    IntegerMachineRun.copied input = input.take 1 ++ PayloadControl.copied .empty (input.drop 1) := by
  cases input <;> rfl

theorem rest_eq (input : List Bool) : NumericCursor.integerRest input = NumericCursor.naturalRest (input.drop 1) := by
  cases input <;> rfl

theorem hoareTime (before input emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ R work out)
      (fun inp work out => Cursor (before ++ IntegerMachineRun.copied input) (NumericCursor.integerRest input)
        emitted inp work out ∧ R work out) (input.length + 3) := by
  have hb := InputBitSkip.hoareTime before input emitted R
  have hn := NaturalSkipRaw.hoareTime (before ++ input.take 1) (input.drop 1) emitted R
  have h := seqTM_hoareTime InputBitSkip.machine NaturalSkip.machine hb (by
    rintro inp work out ⟨hc, hr⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr⟩) hn
  have hlen : (input.drop 1).length ≤ input.length := by simp only [List.length_drop]; omega
  simpa only [machine, copied_eq, rest_eq, List.append_assoc] using
    h.mono_bound (by omega : 1 + 1 + ((input.drop 1).length + 1) ≤ input.length + 3)

theorem encoded_hoareTime (value : ℤ) (before tail emitted : List Bool) (R : (Fin w → Tape) → Tape → Prop) :
    (machine (w := w)).HoareTime
      (fun inp work out => Cursor before (BitCodec.integerCode value ++ tail) emitted inp work out ∧ R work out)
      (fun inp work out => Cursor (before ++ BitCodec.integerCode value) tail emitted inp work out ∧ R work out)
      ((BitCodec.integerCode value ++ tail).length + 3) := by
  simpa only [NumericCursor.integer_copied_code, NumericCursor.integer_rest_code] using
    hoareTime before (BitCodec.integerCode value ++ tail) emitted R

end JointThermoComplexity.Complexity.IntegerSkipRaw

#print axioms JointThermoComplexity.Complexity.IntegerSkipRaw.hoareTime
#print axioms JointThermoComplexity.Complexity.IntegerSkipRaw.encoded_hoareTime
