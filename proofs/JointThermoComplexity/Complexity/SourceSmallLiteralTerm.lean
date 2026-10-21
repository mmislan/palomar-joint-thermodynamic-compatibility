module
public import proofs.JointThermoComplexity.Complexity.SourceLiteralHeight
public import Mathlib.Tactic.Ring

set_option autoImplicit false
@[expose] public section

/-! Binary literals become linear-size terms using only integer literals 0, 1,
and 2. Doubling uses multiplication by 2, so no subtree is duplicated. -/

namespace JointThermoComplexity.Complexity.SourceSmallLiterals
open RealSyntax BitCodec
variable {n : ℕ}

def fromBits : List Bool → Term n
  | [] => .int 0
  | b :: bs => .add (.int (if b then 1 else 0)) (.mul (.int 2) (fromBits bs))

theorem fromBits_eval (bits : List Bool) (ρ : Fin n → ℝ) :
    (fromBits bits).eval ρ = (readBits bits : ℝ) := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [fromBits, Term.eval, readBits, Nat.bit, ih]
    ring

theorem fromBits_height (bits : List Bool) : (fromBits bits : Term n).literalHeight ≤ 2 := by
  induction bits with
  | nil => change 0 ≤ 2; omega
  | cons b bs ih => cases b <;> simpa [fromBits, Term.literalHeight] using ih

theorem fromBits_code_length (bits : List Bool) : (fromBits bits : Term n).code.length ≤ 22 * bits.length + 5 := by
  induction bits with
  | nil => change 5 ≤ 5; rfl
  | cons b bs ih =>
    have h0 : (integerCode 0).length = 2 := rfl
    have h1 : (integerCode 1).length = 4 := rfl
    have h2 : (integerCode 2).length = 6 := rfl
    cases b with
    | false =>
      simp only [fromBits, Bool.false_eq_true, ↓reduceIte, Term.code, List.length_append,
        List.length_cons, List.length_nil, h0, h2]
      omega
    | true =>
      simp only [fromBits, ↓reduceIte, Term.code, List.length_append, List.length_cons,
        List.length_nil, h1, h2]
      omega

def integerTerm (z : ℤ) : Term n :=
  if z < 0 then .neg (fromBits z.natAbs.bits) else fromBits z.natAbs.bits

theorem integerTerm_eval (z : ℤ) (ρ : Fin n → ℝ) : (integerTerm z).eval ρ = (z : ℝ) := by
  cases z with
  | ofNat k => simp [integerTerm, show ¬(k : ℤ) < 0 by omega, fromBits_eval]
  | negSucc k => simp [integerTerm, Term.eval, fromBits_eval]

theorem integerTerm_height (z : ℤ) : (integerTerm z : Term n).literalHeight ≤ 2 := by
  unfold integerTerm
  split
  · exact fromBits_height _
  · exact fromBits_height _

theorem integerTerm_code_length (z : ℤ) :
    (integerTerm z : Term n).code.length ≤ 11 * (Term.int z : Term n).code.length := by
  have h := fromBits_code_length (n := n) z.natAbs.bits
  unfold integerTerm
  split
  · simp only [Term.code, List.length_append, List.length_cons, List.length_nil, integerCode_length]
    omega
  · simp only [Term.code, List.length_append, List.length_cons, List.length_nil, integerCode_length]
    omega

def expandTerm : Term n → Term n
  | .int z => integerTerm z
  | .var i => .var i
  | .add s t => .add (expandTerm s) (expandTerm t)
  | .mul s t => .mul (expandTerm s) (expandTerm t)
  | .neg t => .neg (expandTerm t)

theorem expandTerm_eval (t : Term n) (ρ : Fin n → ℝ) : (expandTerm t).eval ρ = t.eval ρ := by
  induction t with
  | int z => exact integerTerm_eval z ρ
  | var i => rfl
  | add s t hs ht => simp only [expandTerm, Term.eval, hs, ht]
  | mul s t hs ht => simp only [expandTerm, Term.eval, hs, ht]
  | neg t ht => simp only [expandTerm, Term.eval, ht]

theorem expandTerm_height (t : Term n) : (expandTerm t).literalHeight ≤ 2 := by
  induction t with
  | int z => exact integerTerm_height z
  | var i => exact Nat.zero_le _
  | add s t hs ht | mul s t hs ht => exact max_le hs ht
  | neg t ht => exact ht

theorem expandTerm_code_length (t : Term n) : (expandTerm t).code.length ≤ 11 * t.code.length := by
  induction t with
  | int z => exact integerTerm_code_length z
  | var i => change (Term.var i).code.length ≤ 11 * (Term.var i).code.length; omega
  | add s t hs ht | mul s t hs ht =>
    simp only [expandTerm, Term.code, List.length_append, List.length_cons, List.length_nil]
    omega
  | neg t ht =>
    simp only [expandTerm, Term.code, List.length_append, List.length_cons, List.length_nil]
    omega

end JointThermoComplexity.Complexity.SourceSmallLiterals

#print axioms JointThermoComplexity.Complexity.SourceSmallLiterals.integerTerm_eval
#print axioms JointThermoComplexity.Complexity.SourceSmallLiterals.expandTerm_eval
#print axioms JointThermoComplexity.Complexity.SourceSmallLiterals.expandTerm_height
#print axioms JointThermoComplexity.Complexity.SourceSmallLiterals.expandTerm_code_length
