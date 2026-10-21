module
public import proofs.JointThermoComplexity.Complexity.SmallCoefficientMatch
public import proofs.JointThermoComplexity.Complexity.BinaryIncrementRun

set_option autoImplicit false
@[expose] public section

/-! Actual equality of retained canonical binary naturals, without unary expansion. -/

namespace JointThermoComplexity.Complexity.BinaryEqualityFlag
open _root_.Complexity _root_.Complexity.TM BinaryIncrementRun
open HeaderAt (Cursor)
open SmallCoefficientMatch (Ports)
variable {w : ℕ}

def equal (xs ys : List Bool) : Bool := (!(BinaryDifference.subtract xs ys false).2) &&
  (!(BinaryDifference.subtract ys xs false).2)

theorem equal_iff (xs ys : List Bool) : equal xs ys = true ↔ BinaryDifference.value xs = BinaryDifference.value ys := by
  have hnot (b : Bool) : (!b) = true ↔ b = false := by cases b <;> decide
  simp only [equal, Bool.and_eq_true, hnot]
  have h1 := BinaryDifferenceValue.borrow_iff xs ys
  have h2 := BinaryDifferenceValue.borrow_iff ys xs
  constructor
  · rintro ⟨hxy, hyx⟩
    simp only [hxy, Bool.false_eq_true, false_iff] at h1
    simp only [hyx, Bool.false_eq_true, false_iff] at h2
    omega
  · intro he
    constructor
    · cases h : (BinaryDifference.subtract xs ys false).2 with
      | false => rfl
      | true => have := h1.mp h; omega
    · cases h : (BinaryDifference.subtract ys xs false).2 with
      | false => rfl
      | true => have := h2.mp h; omega

theorem unequal_bits (n m : ℕ) : (!(equal n.bits m.bits)) = decide (n ≠ m) := by
  have hiff : equal n.bits m.bits = true ↔ n = m := by
    simpa only [BinaryDifference.value_bits, Int.natCast_inj] using equal_iff n.bits m.bits
  by_cases hn : n = m
  · have he := hiff.mpr hn
    rw [he]
    simp [hn]
  · have he : equal n.bits m.bits = false := by
      cases h : equal n.bits m.bits with
      | false => rfl
      | true => exact False.elim (hn (hiff.mp h))
    rw [he]
    simp [hn]

def Pre (p : Ports w) (n m : ℕ) (before input emitted : List Bool)
    (R : (Fin (w + 1) → Tape) → Prop) : _root_.Complexity.TM.TapePred (w + 1) := fun inp work out =>
  Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧ Register n (work p.operand) ∧
    Register m (work p.constant) ∧ (work p.flag).head = 1 ∧ R work

def machine (p : Ports w) : TM (w + 1) := SmallCoefficientMatch.pairMachine p

theorem hoareTime (p : Ports w) (n m B : ℕ) (hn : n.bits.length ≤ B) (hm : m.bits.length ≤ B)
    (before input emitted : List Bool) (R : (Fin (w + 1) → Tape) → Prop) (hR : SmallCoefficientMatch.Stable p R) :
    (machine p).HoareTime (Pre p n m before input emitted R)
      (fun inp work out => Pre p n m before input emitted R inp work out ∧ (work p.flag).read = Γ.ofBool (decide (n ≠ m)))
      (24 * B + 21) := by
  have h1 := SmallCoefficientMatch.compare_hoareTime p n.bits m.bits B before input emitted R hR
  have h2 := SmallCoefficientMatch.second_hoareTime p n.bits m.bits B before input emitted R hR
  have hall := seqTM_hoareTime _ _ h1 (by
    rintro inp work out hp
    obtain ⟨hi, hw, ho⟩ := hp.1.phase
    rw [hi, hw, ho]
    exact hp) h2
  apply hall.consequence
  · rintro inp work out ⟨hc, hs, hv, hu, hf, hr⟩
    exact ⟨hc, ⟨hs, hv.1, hu.1, hv.2, hu.2, hf⟩, by omega, by omega, hr⟩
  · rintro inp work out ⟨hc, ⟨hs, _, _, hr⟩, hf⟩
    refine ⟨⟨hc, hs.safe, ⟨hs.lhs, hs.lhsZero⟩, ⟨hs.rhs, hs.rhsZero⟩, hs.flagHead, hr⟩, ?_⟩
    change (work p.flag).read = Γ.ofBool (!(equal n.bits m.bits)) at hf
    rw [unequal_bits] at hf
    exact hf
  · omega

end JointThermoComplexity.Complexity.BinaryEqualityFlag

#print axioms JointThermoComplexity.Complexity.BinaryEqualityFlag.hoareTime
#print axioms JointThermoComplexity.Complexity.BinaryEqualityFlag.unequal_bits
