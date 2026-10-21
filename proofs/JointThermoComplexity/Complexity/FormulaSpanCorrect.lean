module
public import proofs.JointThermoComplexity.Complexity.FormulaSpanControl

set_option autoImplicit false
@[expose] public section

/-! The mixed raw traversal returns formulaCount, including unused equality witness coordinates. -/

namespace JointThermoComplexity.Complexity.FormulaSpanCorrect
open RealSyntax SourceCoordinateEnumeration SmallSyntaxForests FormulaSpanControl
variable {n : ℕ}

def formulaCoordinates (ps : List (Formula n)) : ℕ := (ps.map formulaCount).sum
def coordinates (s : Forest n) : ℕ := SourceTermScan.forestNodes s.terms + formulaCoordinates s.formulas
def bump (s : Forest n) : ℕ := match s.terms, s.formulas with
  | _ :: _, _ => 1
  | [], .eq _ _ :: _ | [], .lt _ _ :: _ => 4
  | _, _ => 1

theorem coordinates_next (s : Forest n) (hne : s.terms ≠ [] ∨ s.formulas ≠ []) :
    coordinates s.next + bump s = coordinates s := by
  rcases s with ⟨ts, ps⟩
  cases ts with
  | nil =>
    cases ps with
    | nil => simp at hne
    | cons p ps =>
      cases p <;> simp [coordinates, formulaCoordinates, bump, Forest.next, formulaCount,
        SourceTermScan.forestNodes, SourceFormulaScan.childFormulas] <;> omega
  | cons t ts =>
    have h := SourceTermScan.child_nodes t ts
    change SourceTermScan.forestNodes (SourceTermScan.childTerms t ++ ts) + formulaCoordinates ps + 1 =
      SourceTermScan.forestNodes (t :: ts) + formulaCoordinates ps
    omega

theorem step_forest (s : Forest n) (before suffix : List Bool) (count : ℕ)
    (hne : s.terms ≠ [] ∨ s.formulas ≠ []) :
    step ⟨before, s.code ++ suffix, s.terms.length, s.formulas.length, count⟩ =
      ⟨before ++ s.taken, s.next.code ++ suffix, s.next.terms.length, s.next.formulas.length, count + bump s⟩ := by
  rcases s with ⟨ts, ps⟩
  cases ts with
  | nil =>
    cases ps with
    | nil => simp at hne
    | cons p ps =>
      cases p <;> simp [step, formulaStep, termCount, allocation, SourceFormulaScan.classify,
        Forest.code, Forest.next, Forest.taken, bump, tag, SourceFormulaScan.childFormulas,
        SourceTermScan.forestCode, SourceFormulaScan.forestCode, Formula.code, SourceTermToken.tagBits,
        SourceBitRead.value, SourceTags.accepted, SourceFormulaScan.Kind.children, List.append_assoc]
  | cons t ts =>
    have hw := word_decomposition (Forest.mk (t :: ts) ps)
    have hi : (Forest.mk (t :: ts) ps).code ++ suffix = (SourceTermScan.rootHead t).code ++
        ((Forest.mk (t :: ts) ps).next.code ++ suffix) := by
      rw [← hw, List.append_assoc]
      rfl
    change fromTerm ps.length (TermSpanControl.step ⟨before, (Forest.mk (t :: ts) ps).code ++ suffix,
      (t :: ts).length, count⟩) = _
    rw [hi, List.length_cons, TermSpanControl.step_head]
    have hc := SourceTermScan.child_count t ts
    simp only [fromTerm, Forest.taken, Forest.next, bump, hc]

theorem run_exact (fuel : ℕ) (s : Forest n) (hn : s.nodes = fuel) (before suffix : List Bool) (count : ℕ) :
    run fuel ⟨before, s.code ++ suffix, s.terms.length, s.formulas.length, count⟩ =
      ⟨before ++ s.code, suffix, 0, 0, count + coordinates s⟩ := by
  induction fuel generalizing s before count with
  | zero =>
    have ht : s.terms = [] := by
      by_contra h
      have := nodes_next s (Or.inl h)
      omega
    have hf : s.formulas = [] := by
      by_contra h
      have := nodes_next s (Or.inr h)
      omega
    simp [run, coordinates, formulaCoordinates, Forest.code, ht, hf]
  | succ fuel ih =>
    have hne : s.terms ≠ [] ∨ s.formulas ≠ [] := by
      by_cases ht : s.terms = []
      · by_cases hf : s.formulas = []
        · have hz : s.nodes = 0 := by simp [Forest.nodes, ht, hf, forestTokens]
          omega
        · exact Or.inr hf
      · exact Or.inl ht
    have hn' : s.next.nodes = fuel := by have := nodes_next s hne; omega
    change run fuel (step ⟨before, s.code ++ suffix, s.terms.length, s.formulas.length, count⟩) = _
    rw [step_forest s before suffix count hne, ih s.next hn']
    simp only [List.append_assoc, word_decomposition]
    have hc := coordinates_next s hne
    congr 1
    omega

theorem run_forest (fuel : ℕ) (s : Forest n) (hn : s.nodes ≤ fuel) (before suffix : List Bool) (count : ℕ) :
    run fuel ⟨before, s.code ++ suffix, s.terms.length, s.formulas.length, count⟩ =
      ⟨before ++ s.code, suffix, 0, 0, count + coordinates s⟩ := by
  have he := run_exact s.nodes s rfl before suffix count
  have hf : s.nodes + (fuel - s.nodes) = fuel := by omega
  rw [← hf, run_add, he, run_finished]

theorem run_formula (fuel : ℕ) (p : Formula n) (hn : formulaTokens p ≤ fuel) (before suffix : List Bool) (count : ℕ) :
    run fuel ⟨before, p.code ++ suffix, 0, 1, count⟩ =
      ⟨before ++ p.code, suffix, 0, 0, count + formulaCount p⟩ := by
  let f : Forest n := ⟨[], [p]⟩
  have hnodes : f.nodes ≤ fuel := by simpa [f, Forest.nodes, forestTokens] using hn
  have h := run_forest fuel f hnodes before suffix count
  simpa [f, Forest.code, SourceTermScan.forestCode, SourceFormulaScan.forestCode, coordinates, formulaCoordinates] using h

theorem input_length_fuel (p : Formula n) (before suffix : List Bool) (count : ℕ) :
    run (p.code ++ suffix).length ⟨before, p.code ++ suffix, 0, 1, count⟩ =
      ⟨before ++ p.code, suffix, 0, 0, count + formulaCount p⟩ := by
  exact run_formula _ p (by have := formulaTokens_le_code_length p; rw [List.length_append]; omega) before suffix count

end JointThermoComplexity.Complexity.FormulaSpanCorrect

#print axioms JointThermoComplexity.Complexity.FormulaSpanCorrect.step_forest
#print axioms JointThermoComplexity.Complexity.FormulaSpanCorrect.run_exact
#print axioms JointThermoComplexity.Complexity.FormulaSpanCorrect.input_length_fuel
