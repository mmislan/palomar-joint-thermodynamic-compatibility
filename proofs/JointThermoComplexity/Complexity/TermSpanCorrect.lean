module
public import proofs.JointThermoComplexity.Complexity.TermSpanControl
public import proofs.JointThermoComplexity.Complexity.SourceTermQueueComplete

set_option autoImplicit false
@[expose] public section

/-! Exact node counts and consumed spans are derived from independent term syntax, with arbitrary suffixes. -/

namespace JointThermoComplexity.Complexity.TermSpanCorrect
open RealSyntax SourceTermScan TermSpanControl
variable {n : ℕ}

theorem run_exact (fuel : ℕ) (ts : List (Term n)) (hn : forestNodes ts = fuel)
    (before suffix : List Bool) (nodes : ℕ) :
    run fuel ⟨before, forestCode ts ++ suffix, ts.length, nodes⟩ =
      ⟨before ++ forestCode ts, suffix, 0, nodes + fuel⟩ := by
  induction fuel generalizing ts before nodes with
  | zero =>
    cases ts with
    | nil => simp only [forestCode_nil, List.nil_append, List.append_nil, List.length_nil, Nat.add_zero, run]
    | cons t ts => have h := child_nodes t ts; omega
  | succ fuel ih =>
    cases ts with
    | nil => simp only [forestNodes_nil] at hn; omega
    | cons t ts =>
      have hc := child_nodes t ts
      have hn' : forestNodes (childTerms t ++ ts) = fuel := by omega
      have hword : forestCode (t :: ts) ++ suffix = (rootHead t).code ++ (forestCode (childTerms t ++ ts) ++ suffix) := by
        rw [root_decomposition, List.append_assoc]
      change run fuel (step ⟨before, forestCode (t :: ts) ++ suffix, (t :: ts).length, nodes⟩) = _
      rw [hword, List.length_cons, step_head, ← child_count, ih _ hn']
      simp only [List.append_assoc, ← root_decomposition]
      congr 1
      omega

theorem run_forest (fuel : ℕ) (ts : List (Term n)) (hn : forestNodes ts ≤ fuel)
    (before suffix : List Bool) (nodes : ℕ) :
    run fuel ⟨before, forestCode ts ++ suffix, ts.length, nodes⟩ =
      ⟨before ++ forestCode ts, suffix, 0, nodes + forestNodes ts⟩ := by
  have he := run_exact (forestNodes ts) ts rfl before suffix nodes
  have hf : forestNodes ts + (fuel - forestNodes ts) = fuel := by omega
  rw [← hf, run_add, he, run_finished]

theorem run_term (fuel : ℕ) (t : Term n) (hn : t.size ≤ fuel)
    (before suffix : List Bool) (nodes : ℕ) :
    run fuel ⟨before, t.code ++ suffix, 1, nodes⟩ = ⟨before ++ t.code, suffix, 0, nodes + t.size⟩ := by
  simpa only [forestCode_cons, forestCode_nil, List.append_nil, List.length_cons, List.length_nil,
    forestNodes_cons, forestNodes_nil, Nat.add_zero] using run_forest fuel [t] (by
      simpa only [forestNodes_cons, forestNodes_nil, Nat.add_zero] using hn) before suffix nodes

theorem input_length_fuel (t : Term n) (before suffix : List Bool) (nodes : ℕ) :
    run (t.code ++ suffix).length ⟨before, t.code ++ suffix, 1, nodes⟩ =
      ⟨before ++ t.code, suffix, 0, nodes + t.size⟩ := by
  exact run_term _ t (by have := t.size_le_code_length; rw [List.length_append]; omega) before suffix nodes

end JointThermoComplexity.Complexity.TermSpanCorrect

#print axioms JointThermoComplexity.Complexity.TermSpanCorrect.run_exact
#print axioms JointThermoComplexity.Complexity.TermSpanCorrect.run_forest
#print axioms JointThermoComplexity.Complexity.TermSpanCorrect.input_length_fuel
