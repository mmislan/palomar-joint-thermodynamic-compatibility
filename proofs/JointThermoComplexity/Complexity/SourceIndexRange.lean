module
public import proofs.JointThermoComplexity.Complexity.BinaryCompareRewind
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceValue

set_option autoImplicit false
@[expose] public section

/-! Source variable indices are compared as raw binary payloads. The physical
machine uses no unary representation of the candidate's numeric magnitude. -/

namespace JointThermoComplexity.Complexity.SourceIndexRange
open _root_.Complexity _root_.Complexity.TM HeaderAt
open BinaryDifferenceCursor BinaryDifferenceRuntime

theorem borrow_nat_iff (xs : List Bool) (arity : ℕ) :
    (BinaryDifference.subtract xs arity.bits false).2 = true ↔ BitCodec.readBits xs < arity := by
  have h := BinaryDifferenceValue.borrow_iff xs arity.bits
  rw [BinaryDifference.value_bits] at h
  change (BinaryDifference.subtract xs arity.bits false).2 = true ↔
    (BitCodec.readBits xs : ℤ) < (arity : ℤ) at h
  constructor
  · intro hb; have hv := h.mp hb; omega
  · intro hv; apply h.mpr; omega

theorem range_flag_eq (xs : List Bool) (arity : ℕ) :
    (BinaryDifference.subtract xs arity.bits false).2 = decide (BitCodec.readBits xs < arity) := by
  cases hb : (BinaryDifference.subtract xs arity.bits false).2 with
  | false =>
    have hn : ¬BitCodec.readBits xs < arity := by
      intro hi
      have he := (borrow_nat_iff xs arity).mpr hi
      rw [hb] at he
      cases he
    simp only [hn, decide_false]
  | true =>
    have hi := (borrow_nat_iff xs arity).mp hb
    simp only [hi, decide_true]

variable {w : ℕ}

def machine (left right flag : Fin w) : TM w := BinaryCompareRewind.machine left right flag

theorem hoareTime (L : ℕ) (left right flag : Fin w) (sep : Separate left right flag)
    (xs : List Bool) (arity : ℕ) (hx : xs.length ≤ L) (ha : arity.bits.length ≤ L)
    (before input emitted : List Bool) (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ left → j ≠ right → j ≠ flag → work' j = work j) → R work → R work') :
    (machine left right flag).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Start left right flag xs arity.bits work ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧ Start left right flag xs arity.bits work ∧
        (work flag).read = Γ.ofBool (decide (BitCodec.readBits xs < arity)) ∧ R work) (3 * L + 9) := by
  have h := BinaryCompareRewind.hoareTime left right flag sep xs arity.bits before input emitted R hR
  exact h.consequence (fun _ _ _ hp => hp) (by
    rintro inp work out ⟨hc, hs, hf, hr⟩
    exact ⟨hc, hs, by simpa only [range_flag_eq] using hf, hr⟩) (by
      unfold BinaryCompareRewind.timeBound
      have hm : max xs.length arity.bits.length ≤ L := max_le hx ha
      omega)

end JointThermoComplexity.Complexity.SourceIndexRange

#print axioms JointThermoComplexity.Complexity.SourceIndexRange.range_flag_eq
#print axioms JointThermoComplexity.Complexity.SourceIndexRange.hoareTime
