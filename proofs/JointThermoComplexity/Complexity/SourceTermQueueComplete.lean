module
public import proofs.JointThermoComplexity.Complexity.SourceTermQueueSound

set_option autoImplicit false
@[expose] public section

/-! The pending-node scanner accepts exactly canonical term forests and needs
at most their syntax-node count, hence at most the binary input length. -/

namespace JointThermoComplexity.Complexity.SourceTermScan
open RealSyntax
variable {n : ℕ}

def rootHead : Term n → Head n
  | .int z => .int z
  | .var i => .var i
  | .add _ _ => .add
  | .mul _ _ => .mul
  | .neg _ => .neg

def childTerms : Term n → List (Term n)
  | .int _ | .var _ => []
  | .add s t | .mul s t => [s, t]
  | .neg t => [t]

theorem root_decomposition (t : Term n) (ts : List (Term n)) :
    forestCode (t :: ts) = (rootHead t).code ++ forestCode (childTerms t ++ ts) := by
  cases t <;> simp [rootHead, childTerms, forestCode, Term.code, Head.code, List.append_assoc]

theorem child_count (t : Term n) (ts : List (Term n)) :
    (childTerms t ++ ts).length = ts.length + (rootHead t).children := by
  cases t <;> simp only [childTerms, rootHead, Head.children, List.length_append,
    List.length_cons, List.length_nil] <;> omega

theorem child_nodes (t : Term n) (ts : List (Term n)) :
    forestNodes (childTerms t ++ ts) + 1 = forestNodes (t :: ts) := by
  cases t <;> simp only [childTerms, List.nil_append, List.cons_append, forestNodes_cons,
    Term.size] <;> omega

theorem scan_complete (fuel : ℕ) (ts : List (Term n)) (suffix : List Bool) (hf : forestNodes ts ≤ fuel) :
    scan n fuel ts.length (forestCode ts ++ suffix) = some suffix := by
  induction fuel generalizing ts suffix with
  | zero =>
    cases ts with
    | nil => rfl
    | cons t ts =>
      have he := child_nodes t ts
      omega
  | succ fuel ih =>
    cases ts with
    | nil => rfl
    | cons t ts =>
      have he := child_nodes t ts
      have hn : forestNodes (childTerms t ++ ts) ≤ fuel := by omega
      have hrest := ih (childTerms t ++ ts) suffix hn
      have hc : forestCode (t :: ts) ++ suffix = (rootHead t).code ++ (forestCode (childTerms t ++ ts) ++ suffix) := by
        rw [root_decomposition, List.append_assoc]
      rw [hc]
      have hstep := scan_step (fuel := fuel) (pending := ts.length)
        (parseHead_code (rootHead t) (forestCode (childTerms t ++ ts) ++ suffix))
      rw [List.length_cons, hstep, ← child_count]
      exact hrest

theorem scan_some_iff (fuel pending : ℕ) (input suffix : List Bool) :
    scan n fuel pending input = some suffix ↔
      ∃ ts : List (Term n), ts.length = pending ∧ forestNodes ts ≤ fuel ∧ input = forestCode ts ++ suffix := by
  constructor
  · exact scan_sound fuel pending input suffix
  · rintro ⟨ts, hcount, hnodes, hcode⟩
    rw [← hcount, hcode]
    exact scan_complete fuel ts suffix hnodes

theorem scan_forest_input_length (ts : List (Term n)) (suffix : List Bool) :
    scan n (forestCode ts ++ suffix).length ts.length (forestCode ts ++ suffix) = some suffix := by
  apply scan_complete
  have h := forestNodes_le_code_length ts
  rw [List.length_append]
  omega

end JointThermoComplexity.Complexity.SourceTermScan

#print axioms JointThermoComplexity.Complexity.SourceTermScan.scan_complete
#print axioms JointThermoComplexity.Complexity.SourceTermScan.scan_some_iff
#print axioms JointThermoComplexity.Complexity.SourceTermScan.scan_forest_input_length
