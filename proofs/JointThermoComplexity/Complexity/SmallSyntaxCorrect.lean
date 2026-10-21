module
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxForests
public import proofs.JointThermoComplexity.Complexity.SmallSyntaxControl

set_option autoImplicit false
@[expose] public section

/-! Exact independent typed expansion for the total bounded streaming control. Machine runtime is separate. -/

namespace JointThermoComplexity.Complexity.SmallSyntaxCorrect
open RealSyntax SmallSyntaxForests SmallSyntaxControl
variable {n : ℕ}

theorem run_exact_forest (fuel : ℕ) (s : Forest n) (hn : s.nodes = fuel) (before suffix emitted : List Bool) :
    run fuel ⟨before, s.code ++ suffix, emitted, s.terms.length⟩ =
      ⟨before ++ s.code, suffix, emitted ++ s.expanded, 0⟩ := by
  induction fuel generalizing s before suffix emitted with
  | zero =>
    have ht : s.terms = [] := by
      by_contra ht
      have h := nodes_next s (Or.inl ht)
      omega
    have hf : s.formulas = [] := by
      by_contra hf
      have h := nodes_next s (Or.inr hf)
      omega
    simp [run, Forest.code, Forest.expanded, expandedTerms, expandedFormulas, ht, hf]
  | succ fuel ih =>
    have hne : s.terms ≠ [] ∨ s.formulas ≠ [] := by
      by_cases ht : s.terms = []
      · by_cases hf : s.formulas = []
        · have hz : s.nodes = 0 := by simp [Forest.nodes, ht, hf, forestTokens]
          omega
        · exact Or.inr hf
      · exact Or.inl ht
    have hn' : s.next.nodes = fuel := by have h := nodes_next s hne; omega
    have ht := token_result s suffix hne
    have hs : step ⟨before, s.code ++ suffix, emitted, s.terms.length⟩ =
        ⟨before ++ s.taken, s.next.code ++ suffix, emitted ++ s.output, s.next.terms.length⟩ := by
      simp only [SmallSyntaxControl.step, ht]
    have hrec := ih (s := s.next) (before := before ++ s.taken) (suffix := suffix) (emitted := emitted ++ s.output) hn'
    change run fuel (step ⟨before, s.code ++ suffix, emitted, s.terms.length⟩) = _
    rw [hs, hrec]
    simp only [List.append_assoc, word_decomposition, output_decomposition]

theorem run_forest (fuel : ℕ) (s : Forest n) (hn : s.nodes ≤ fuel) (before emitted : List Bool) :
    run fuel ⟨before, s.code, emitted, s.terms.length⟩ = ⟨before ++ s.code, [], emitted ++ s.expanded, 0⟩ := by
  have he := run_exact_forest s.nodes s rfl before [] emitted
  simp only [List.append_nil] at he
  have hf : s.nodes + (fuel - s.nodes) = fuel := by omega
  rw [← hf, run_add, he, run_empty]

theorem code_sentence (s : Sentence) : SmallSyntaxControl.code s.code = (SourceSmallLiterals.expandSentence s).code := by
  rcases s with ⟨arity, p⟩
  let f : Forest arity := ⟨[], [p]⟩
  have hlen : p.code.length ≤ (Sentence.mk arity p).code.length := by
    simp only [Sentence.code, List.length_append]
    omega
  have hn : f.nodes ≤ (Sentence.mk arity p).code.length := by
    have h := nodes_le_code_length f
    have hc : f.code = p.code := by simp [f, Forest.code, SourceTermScan.forestCode, SourceFormulaScan.forestCode]
    rw [hc] at h
    exact h.trans hlen
  have he := run_forest (Sentence.mk arity p).code.length f hn (binderCode arity) (binderCode arity)
  have ho := congrArg State.emitted he
  simpa [SmallSyntaxControl.code, Sentence.code, HeaderControl.copied_code, HeaderControl.suffix_code,
    SourceSmallLiterals.expandSentence, f, Forest.code, Forest.expanded, SourceTermScan.forestCode,
    SourceFormulaScan.forestCode, expandedTerms, expandedFormulas] using ho

theorem normalized_code (input : List Bool) :
    SmallSyntaxControl.code (SourceNormalizationFP.code input) = (SourceSmallLiterals.normalizeSmall input).code :=
  code_sentence (SourceNormalization.normalize input)

end JointThermoComplexity.Complexity.SmallSyntaxCorrect

#print axioms JointThermoComplexity.Complexity.SmallSyntaxCorrect.run_exact_forest
#print axioms JointThermoComplexity.Complexity.SmallSyntaxCorrect.code_sentence
#print axioms JointThermoComplexity.Complexity.SmallSyntaxCorrect.normalized_code
