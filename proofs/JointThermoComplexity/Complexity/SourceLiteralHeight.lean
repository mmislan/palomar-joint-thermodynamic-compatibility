module
public import proofs.JointThermoComplexity.Complexity.RealSyntaxSize
public import Mathlib.Data.Nat.Size

set_option autoImplicit false
@[expose] public section

/-! # Literal magnitudes controlled by the actual source binary encoding -/

namespace JointThermoComplexity.Complexity.RealSyntax
open BitCodec
variable {n : ℕ}

def Term.literalHeight : Term n → ℕ
  | .int z => z.natAbs
  | .var _ => 0
  | .add s t | .mul s t => max s.literalHeight t.literalHeight
  | .neg t => t.literalHeight

def Formula.literalHeight : Formula n → ℕ
  | .truth | .falsity => 0
  | .eq s t | .lt s t => max s.literalHeight t.literalHeight
  | .conj p q | .disj p q => max p.literalHeight q.literalHeight

theorem Term.literalHeight_le_pow_code_length (t : Term n) :
    t.literalHeight ≤ 2 ^ t.code.length := by
  induction t with
  | int z =>
    have h : z.natAbs < 2 ^ z.natAbs.bits.length := by
      simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self z.natAbs
    have hl : z.natAbs.bits.length ≤ (Term.int z : Term n).code.length := by
      simp only [Term.code, List.length_append, List.length_cons, List.length_nil,
        integerCode_length]
      omega
    exact h.le.trans (Nat.pow_le_pow_right (by decide) hl)
  | var i => exact Nat.zero_le _
  | add s t hs ht | mul s t hs ht =>
    apply max_le
    · exact hs.trans (Nat.pow_le_pow_right (by decide) (by
        simp only [Term.code, List.length_append, List.length_cons, List.length_nil]; omega))
    · exact ht.trans (Nat.pow_le_pow_right (by decide) (by
        simp only [Term.code, List.length_append, List.length_cons, List.length_nil]; omega))
  | neg t ht =>
    exact ht.trans (Nat.pow_le_pow_right (by decide) (by
      simp only [Term.code, List.length_append, List.length_cons, List.length_nil]; omega))

theorem Formula.literalHeight_le_pow_code_length (p : Formula n) :
    p.literalHeight ≤ 2 ^ p.code.length := by
  induction p with
  | truth | falsity => exact Nat.zero_le _
  | eq s t | lt s t =>
    apply max_le
    · exact s.literalHeight_le_pow_code_length.trans
        (Nat.pow_le_pow_right (by decide) (by
          simp only [Formula.code, List.length_append, List.length_cons, List.length_nil]; omega))
    · exact t.literalHeight_le_pow_code_length.trans
        (Nat.pow_le_pow_right (by decide) (by
          simp only [Formula.code, List.length_append, List.length_cons, List.length_nil]; omega))
  | conj p q hp hq | disj p q hp hq =>
    apply max_le
    · exact hp.trans (Nat.pow_le_pow_right (by decide) (by
        simp only [Formula.code, List.length_append, List.length_cons, List.length_nil]; omega))
    · exact hq.trans (Nat.pow_le_pow_right (by decide) (by
        simp only [Formula.code, List.length_append, List.length_cons, List.length_nil]; omega))

theorem Sentence.literalHeight_le_pow_code_length (s : Sentence) :
    s.formula.literalHeight ≤ 2 ^ s.code.length :=
  s.formula.literalHeight_le_pow_code_length.trans (Nat.pow_le_pow_right (by decide) (by
    simp only [Sentence.code, List.length_append]; omega))

end JointThermoComplexity.Complexity.RealSyntax

#print axioms JointThermoComplexity.Complexity.RealSyntax.Term.literalHeight_le_pow_code_length
#print axioms JointThermoComplexity.Complexity.RealSyntax.Sentence.literalHeight_le_pow_code_length
