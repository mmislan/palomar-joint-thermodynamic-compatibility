module
public import proofs.JointThermoComplexity.Complexity.SourceSmallLiteralTerm
public import proofs.JointThermoComplexity.Complexity.SourceNormalization

set_option autoImplicit false
@[expose] public section

/-! Semantic and linear code-size guarantees for constant-sized source literals.
The original source language and the existing typed strict maps stay unchanged. -/

namespace JointThermoComplexity.Complexity.SourceSmallLiterals
open RealSyntax SourceNormalization
variable {n : ℕ}

def expandFormula : Formula n → Formula n
  | .truth => .truth
  | .falsity => .falsity
  | .eq s t => .eq (expandTerm s) (expandTerm t)
  | .lt s t => .lt (expandTerm s) (expandTerm t)
  | .conj p q => .conj (expandFormula p) (expandFormula q)
  | .disj p q => .disj (expandFormula p) (expandFormula q)

theorem expandFormula_eval (p : Formula n) (ρ : Fin n → ℝ) : (expandFormula p).eval ρ ↔ p.eval ρ := by
  induction p with
  | truth | falsity => rfl
  | eq s t => simp only [expandFormula, Formula.eval, expandTerm_eval]
  | lt s t => simp only [expandFormula, Formula.eval, expandTerm_eval]
  | conj p q hp hq => exact and_congr hp hq
  | disj p q hp hq => exact or_congr hp hq

theorem expandFormula_height (p : Formula n) : (expandFormula p).literalHeight ≤ 2 := by
  induction p with
  | truth | falsity => exact Nat.zero_le _
  | eq s t | lt s t => exact max_le (expandTerm_height s) (expandTerm_height t)
  | conj p q hp hq | disj p q hp hq => exact max_le hp hq

theorem expandFormula_code_length (p : Formula n) : (expandFormula p).code.length ≤ 11 * p.code.length := by
  induction p with
  | truth | falsity => change 3 ≤ 11 * 3; omega
  | eq s t | lt s t =>
    have hs := expandTerm_code_length s
    have ht := expandTerm_code_length t
    simp only [expandFormula, Formula.code, List.length_append, List.length_cons, List.length_nil]
    omega
  | conj p q hp hq | disj p q hp hq =>
    simp only [expandFormula, Formula.code, List.length_append, List.length_cons, List.length_nil]
    omega

def expandSentence (s : Sentence) : Sentence := ⟨s.arity, expandFormula s.formula⟩

theorem expandSentence_satisfiable (s : Sentence) : (expandSentence s).Satisfiable ↔ s.Satisfiable := by
  apply exists_congr
  intro ρ
  exact expandFormula_eval s.formula ρ

theorem expandSentence_height (s : Sentence) : (expandSentence s).formula.literalHeight ≤ 2 := expandFormula_height _

theorem expandSentence_code_length (s : Sentence) : (expandSentence s).code.length ≤ 11 * s.code.length := by
  have h := expandFormula_code_length s.formula
  simp only [expandSentence, Sentence.code, List.length_append]
  omega

def normalizeSmall (input : List Bool) : Sentence := expandSentence (normalize input)

theorem normalizeSmall_satisfiable (input : List Bool) : (normalizeSmall input).Satisfiable ↔ input ∈ ETR :=
  (expandSentence_satisfiable _).trans (normalize_satisfiable_iff input)

theorem normalizeSmall_height (input : List Bool) : (normalizeSmall input).formula.literalHeight ≤ 2 :=
  expandSentence_height _

theorem normalizeSmall_code_length (input : List Bool) : (normalizeSmall input).code.length ≤ 11 * (input.length + 4) :=
  Nat.le_trans (expandSentence_code_length _) (Nat.mul_le_mul_left 11 (normalize_code_length input))

end JointThermoComplexity.Complexity.SourceSmallLiterals

#print axioms JointThermoComplexity.Complexity.SourceSmallLiterals.expandSentence_satisfiable
#print axioms JointThermoComplexity.Complexity.SourceSmallLiterals.expandSentence_height
#print axioms JointThermoComplexity.Complexity.SourceSmallLiterals.expandSentence_code_length
#print axioms JointThermoComplexity.Complexity.SourceSmallLiterals.normalizeSmall_satisfiable
#print axioms JointThermoComplexity.Complexity.SourceSmallLiterals.normalizeSmall_code_length
