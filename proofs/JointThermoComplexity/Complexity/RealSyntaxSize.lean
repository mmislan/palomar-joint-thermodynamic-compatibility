module
public import proofs.JointThermoComplexity.Complexity.RealSyntax

set_option autoImplicit false
@[expose] public section

/-! # Syntax-node counts bounded by the independently specified binary encoding -/

namespace JointThermoComplexity.Complexity.RealSyntax
variable {n : ℕ}

def Term.size : Term n → ℕ
  | .int _ | .var _ => 1
  | .add s t | .mul s t => 1 + s.size + t.size
  | .neg t => 1 + t.size

def Formula.size : Formula n → ℕ
  | .truth | .falsity => 1
  | .eq s t | .lt s t => 1 + s.size + t.size
  | .conj p q | .disj p q => 1 + p.size + q.size

theorem Term.size_le_code_length (t : Term n) : t.size ≤ t.code.length := by
  induction t <;> simp_all only [Term.size, Term.code, List.length_append,
    List.length_cons, List.length_nil] <;> omega

theorem Formula.size_le_code_length (p : Formula n) : p.size ≤ p.code.length := by
  induction p with
  | truth | falsity => change 1 ≤ 3; omega
  | eq s t | lt s t =>
    have hs := s.size_le_code_length
    have ht := t.size_le_code_length
    simp only [Formula.size, Formula.code, List.length_append, List.length_cons, List.length_nil]
    omega
  | conj p q hp hq | disj p q hp hq =>
    simp only [Formula.size, Formula.code, List.length_append, List.length_cons, List.length_nil]
    omega

end JointThermoComplexity.Complexity.RealSyntax

#print axioms JointThermoComplexity.Complexity.RealSyntax.Term.size_le_code_length
#print axioms JointThermoComplexity.Complexity.RealSyntax.Formula.size_le_code_length
