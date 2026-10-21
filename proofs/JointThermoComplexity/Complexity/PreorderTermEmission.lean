module
public import proofs.JointThermoComplexity.Complexity.PreorderEmissionControl

set_option autoImplicit false
@[expose] public section

/-! Exact forward term rows with the three reserved atomic witnesses discounted from each live term address. -/

namespace JointThermoComplexity.Complexity.PreorderTermEmission
open RealSyntax SparseInteger PreorderLocalRows PreorderEmissionControl SourceTermScan
variable {n : ℕ}

def termForest : List (Term n) → ℕ → List (Poly ℕ)
  | [], _ => []
  | t :: ts, offset => PreorderTermEquations.equations t Fin.val offset ++ termForest ts (offset + t.size)

theorem forest_head (t : Term n) (ts : List (Term n)) (offset : ℕ) :
    termForest (t :: ts) offset = termLocal t offset ++ termForest (childTerms t ++ ts) (offset + 1) := by
  cases t <;> simp [termForest, termLocal, PreorderTermEquations.equations, childTerms, Term.size,
    List.append_assoc, Nat.add_assoc]

theorem child_height (t u : Term n) (hu : u ∈ childTerms t) : u.literalHeight ≤ t.literalHeight := by
  cases t with
  | int z | var i => simp [childTerms] at hu
  | add a b | mul a b =>
    have he : u = a ∨ u = b := by simpa only [childTerms, List.mem_cons, List.not_mem_nil, or_false] using hu
    rcases he with rfl | rfl
    · exact Nat.le_max_left _ _
    · exact Nat.le_max_right _ _
  | neg a =>
    have he : u = a := by simpa only [childTerms, List.mem_singleton] using hu
    subst u
    exact le_rfl

theorem step_terms (L : ℕ) (t : Term n) (ts : List (Term n)) (before suffix : List Bool)
    (offset forms : ℕ) (rows : Rows) (hlen : (forestCode (t :: ts) ++ suffix).length ≤ L) (hh : t.literalHeight ≤ 2) :
    step L n ⟨⟨before, forestCode (t :: ts) ++ suffix, (t :: ts).length, forms, offset + 3⟩, rows⟩ =
      ⟨⟨before ++ (rootHead t).code, forestCode (childTerms t ++ ts) ++ suffix,
        (childTerms t ++ ts).length, forms, offset + 4⟩, rows ++ words (termLocal t (n + offset))⟩ := by
  have hword : forestCode (t :: ts) ++ suffix = (rootHead t).code ++ (forestCode (childTerms t ++ ts) ++ suffix) := by
    rw [root_decomposition, List.append_assoc]
  have hscan : FormulaSpanControl.step ⟨before, forestCode (t :: ts) ++ suffix, (t :: ts).length, forms, offset + 3⟩ =
      ⟨before ++ (rootHead t).code, forestCode (childTerms t ++ ts) ++ suffix, (childTerms t ++ ts).length, forms, offset + 4⟩ := by
    change FormulaSpanControl.fromTerm forms (TermSpanControl.step
      ⟨before, forestCode (t :: ts) ++ suffix, (t :: ts).length, offset + 3⟩) = _
    rw [hword, List.length_cons, TermSpanControl.step_head, ← child_count]
    rfl
  have hrows : localRows L n ⟨before, forestCode (t :: ts) ++ suffix, (t :: ts).length, forms, offset + 3⟩ =
      words (termLocal t (n + offset)) := by
    simp only [localRows, List.length_cons, term_address]
    have h := PreorderLocalRows.term_code L (n + offset) t (forestCode ts ++ suffix)
      (by simpa only [forestCode_cons, List.append_assoc] using hlen) hh
    simpa only [forestCode_cons, List.append_assoc] using h
  simp only [step, hscan, hrows]

theorem run_terms (fuel : ℕ) (ts : List (Term n)) (hn : forestNodes ts = fuel) (L : ℕ)
    (before suffix : List Bool) (offset forms : ℕ) (rows : Rows)
    (hlen : (forestCode ts ++ suffix).length ≤ L) (hh : ∀ t ∈ ts, t.literalHeight ≤ 2) :
    run L n fuel ⟨⟨before, forestCode ts ++ suffix, ts.length, forms, offset + 3⟩, rows⟩ =
      ⟨⟨before ++ forestCode ts, suffix, 0, forms, offset + 3 + fuel⟩, rows ++ words (termForest ts (n + offset))⟩ := by
  induction fuel generalizing ts before offset rows with
  | zero =>
    cases ts with
    | nil => simp [run, termForest, words]
    | cons t ts => have h := child_nodes t ts; omega
  | succ fuel ih =>
    cases ts with
    | nil => simp only [forestNodes_nil] at hn; omega
    | cons t ts =>
      have hnodes := child_nodes t ts
      have hn' : forestNodes (childTerms t ++ ts) = fuel := by omega
      have hlen' : (forestCode (childTerms t ++ ts) ++ suffix).length ≤ L := by
        rw [root_decomposition, List.append_assoc, List.length_append] at hlen
        omega
      have hh' : ∀ u ∈ childTerms t ++ ts, u.literalHeight ≤ 2 := by
        intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact (child_height t u hu).trans (hh t List.mem_cons_self)
        · exact hh u (List.mem_cons_of_mem t hu)
      change run L n fuel (step L n _) = _
      rw [step_terms L t ts before suffix offset forms rows hlen (hh t List.mem_cons_self)]
      have hrec := ih (ts := childTerms t ++ ts) (before := before ++ (rootHead t).code)
        (offset := offset + 1) (rows := rows ++ words (termLocal t (n + offset))) hn' hlen' hh'
      have hbefore : (before ++ (rootHead t).code) ++ forestCode (childTerms t ++ ts) = before ++ forestCode (t :: ts) := by
        rw [List.append_assoc, ← root_decomposition]
      have hout : (rows ++ words (termLocal t (n + offset))) ++ words (termForest (childTerms t ++ ts) (n + (offset + 1))) =
          rows ++ words (termForest (t :: ts) (n + offset)) := by
        rw [forest_head t ts (n + offset)]
        simp only [words, List.map_append, List.append_assoc, Nat.add_assoc]
      have hc : offset + 1 + 3 + fuel = offset + 3 + (fuel + 1) := by omega
      simpa only [hbefore, hout, hc] using hrec

end JointThermoComplexity.Complexity.PreorderTermEmission

#print axioms JointThermoComplexity.Complexity.PreorderTermEmission.step_terms
#print axioms JointThermoComplexity.Complexity.PreorderTermEmission.run_terms
