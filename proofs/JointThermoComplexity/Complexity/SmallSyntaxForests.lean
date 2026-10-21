module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxToken

set_option autoImplicit false
@[expose] public section

/-! Ghost forests specify expansion without adding any certificate or runtime tape. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxForests
open RealSyntax SourceSmallLiterals
variable {n : ℕ}

def formulaTokens : Formula n → ℕ
  | .truth | .falsity => 1
  | .eq a b | .lt a b => 1 + a.size + b.size
  | .conj p q | .disj p q => 1 + formulaTokens p + formulaTokens q

def forestTokens (ps : List (Formula n)) : ℕ := (ps.map formulaTokens).sum
def expandedTerms (ts : List (Term n)) : List Bool := ts.flatMap (fun t => (expandTerm t).code)
def expandedFormulas (ps : List (Formula n)) : List Bool := ps.flatMap (fun p => (expandFormula p).code)

structure Forest (n : ℕ) where
  terms : List (Term n)
  formulas : List (Formula n)

def Forest.code (s : Forest n) : List Bool := SourceTermScan.forestCode s.terms ++ SourceFormulaScan.forestCode s.formulas
def Forest.expanded (s : Forest n) : List Bool := expandedTerms s.terms ++ expandedFormulas s.formulas
def Forest.nodes (s : Forest n) : ℕ := SourceTermScan.forestNodes s.terms + forestTokens s.formulas

def tag : Formula n → List Bool
  | .truth => [false, false, false]
  | .falsity => [false, false, true]
  | .eq _ _ => [false, true, false]
  | .lt _ _ => [false, true, true]
  | .conj _ _ => [true, false, false]
  | .disj _ _ => [true, false, true]

def Forest.next (s : Forest n) : Forest n := match s.terms, s.formulas with
  | t :: ts, ps => ⟨SourceTermScan.childTerms t ++ ts, ps⟩
  | [], .eq a b :: ps | [], .lt a b :: ps => ⟨[a, b], ps⟩
  | [], p :: ps => ⟨[], SourceFormulaScan.childFormulas p ++ ps⟩
  | [], [] => s

def Forest.taken (s : Forest n) : List Bool := match s.terms, s.formulas with
  | t :: _, _ => (SourceTermScan.rootHead t).code
  | [], p :: _ => tag p
  | [], [] => []

def Forest.output (s : Forest n) : List Bool := match s.terms, s.formulas with
  | t :: _, _ => SmallSyntaxToken.headOutput (SourceTermScan.rootHead t)
  | [], p :: _ => tag p
  | [], [] => []

theorem formulaTokens_le_code_length (p : Formula n) : formulaTokens p ≤ p.code.length := by
  induction p with
  | truth | falsity => change 1 ≤ 3; omega
  | eq a b | lt a b =>
    have ha := a.size_le_code_length
    have hb := b.size_le_code_length
    simp only [formulaTokens, Formula.code, List.length_append, List.length_cons, List.length_nil]
    omega
  | conj p q hp hq | disj p q hp hq =>
    simp only [formulaTokens, Formula.code, List.length_append, List.length_cons, List.length_nil]
    omega

theorem forestTokens_le_code_length (ps : List (Formula n)) : forestTokens ps ≤ (SourceFormulaScan.forestCode ps).length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp := formulaTokens_le_code_length p
    simp only [forestTokens, List.map_cons, List.sum_cons, SourceFormulaScan.forestCode_cons, List.length_append] at *
    omega

theorem nodes_le_code_length (s : Forest n) : s.nodes ≤ s.code.length := by
  have ht := SourceTermScan.forestNodes_le_code_length s.terms
  have hf := forestTokens_le_code_length s.formulas
  unfold Forest.nodes Forest.code
  rw [List.length_append]
  omega

theorem nodes_next (s : Forest n) (hn : s.terms ≠ [] ∨ s.formulas ≠ []) : s.next.nodes + 1 = s.nodes := by
  rcases s with ⟨ts, ps⟩
  cases ts with
  | nil =>
    cases ps with
    | nil => simp at hn
    | cons p ps =>
      cases p <;> simp [Forest.next, Forest.nodes, forestTokens, formulaTokens, SourceFormulaScan.childFormulas,
        SourceTermScan.forestNodes] <;> omega
  | cons t ts =>
    have ht := SourceTermScan.child_nodes t ts
    change SourceTermScan.forestNodes (SourceTermScan.childTerms t ++ ts) + forestTokens ps + 1 =
      SourceTermScan.forestNodes (t :: ts) + forestTokens ps
    omega

theorem word_decomposition (s : Forest n) : s.taken ++ s.next.code = s.code := by
  rcases s with ⟨ts, ps⟩
  cases ts with
  | nil =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      cases p <;> simp [Forest.taken, Forest.next, Forest.code, tag, SourceFormulaScan.childFormulas,
        SourceTermScan.forestCode, SourceFormulaScan.forestCode, Formula.code, List.append_assoc]
  | cons t ts =>
    change (SourceTermScan.rootHead t).code ++
      (SourceTermScan.forestCode (SourceTermScan.childTerms t ++ ts) ++ SourceFormulaScan.forestCode ps) =
      SourceTermScan.forestCode (t :: ts) ++ SourceFormulaScan.forestCode ps
    rw [← List.append_assoc, ← SourceTermScan.root_decomposition]

theorem output_decomposition (s : Forest n) : s.output ++ s.next.expanded = s.expanded := by
  rcases s with ⟨ts, ps⟩
  cases ts with
  | nil =>
    cases ps with
    | nil => rfl
    | cons p ps =>
      cases p <;> simp [Forest.output, Forest.next, Forest.expanded, expandedTerms, expandedFormulas,
        tag, SourceFormulaScan.childFormulas, expandFormula, Formula.code, List.append_assoc]
  | cons t ts =>
    cases t <;> simp [Forest.output, Forest.next, Forest.expanded, expandedTerms, expandedFormulas,
      SmallSyntaxToken.headOutput, SourceTermScan.rootHead, SourceTermScan.Head.code, SourceTermScan.childTerms,
      expandTerm, Term.code, List.append_assoc]

theorem token_result (s : Forest n) (suffix : List Bool) (hn : s.terms ≠ [] ∨ s.formulas ≠ []) :
    SmallSyntaxToken.step s.terms.length (s.code ++ suffix) =
      ⟨s.taken, s.next.code ++ suffix, s.output, s.next.terms.length⟩ := by
  rcases s with ⟨ts, ps⟩
  cases ts with
  | nil =>
    cases ps with
    | nil => simp at hn
    | cons p ps =>
      cases p <;> simp [Forest.code, Forest.next, Forest.taken, Forest.output, tag, SourceFormulaScan.childFormulas,
        SourceTermScan.forestCode, SourceFormulaScan.forestCode, Formula.code, SmallSyntaxToken.tag_step,
        SmallSyntaxToken.body, SmallSyntaxToken.formulaBody, SourceFormulaScan.classify, List.append_assoc]
  | cons t ts =>
    have hc := word_decomposition (Forest.mk (t :: ts) ps)
    have hi : (Forest.mk (t :: ts) ps).code ++ suffix = (SourceTermScan.rootHead t).code ++
        ((Forest.mk (t :: ts) ps).next.code ++ suffix) := by
      rw [← hc, List.append_assoc]
      rfl
    rw [hi, List.length_cons, SmallSyntaxToken.term_head]
    have hp := SourceTermScan.child_count t ts
    simp only [Forest.taken, Forest.output, Forest.next, hp]

end JointThermoComplexity.Complexity.SmallSyntaxForests

#print axioms JointThermoComplexity.Complexity.SmallSyntaxForests.nodes_next
#print axioms JointThermoComplexity.Complexity.SmallSyntaxForests.output_decomposition
#print axioms JointThermoComplexity.Complexity.SmallSyntaxForests.token_result
