module
public import proofs.JointThermoComplexity.Complexity.FormulaSpanLoop

set_option autoImplicit false
@[expose] public section

/-! Bounded raw lookahead queries use the already realized read-only traversal controls. -/

namespace JointThermoComplexity.Complexity.PreorderLookahead
open RealSyntax SourceCoordinateEnumeration

def termResult (L : ℕ) (input : List Bool) : TermSpanControl.State := TermSpanControl.run L ⟨[], input, 1, 0⟩
def termSize (L : ℕ) (input : List Bool) : ℕ := (termResult L input).nodes
def termRest (L : ℕ) (input : List Bool) : List Bool := (termResult L input).input
def formulaResult (L : ℕ) (input : List Bool) : FormulaSpanControl.State := FormulaSpanControl.run L ⟨[], input, 0, 1, 0⟩
def formulaSize (L : ℕ) (input : List Bool) : ℕ := (formulaResult L input).coordinates

theorem term_bounds (L : ℕ) (input : List Bool) : termSize L input ≤ L ∧ (termRest L input).length ≤ input.length := by
  have h := TermSpanControl.run_bounds L ⟨[], input, 1, 0⟩
  exact ⟨by simpa only [termSize, termResult, Nat.zero_add] using h.2.1, h.2.2.1⟩

theorem formula_bound (L : ℕ) (input : List Bool) : formulaSize L input ≤ 4 * L := by
  have h := FormulaSpanControl.run_bounds L ⟨[], input, 0, 1, 0⟩
  simpa only [formulaSize, formulaResult, Nat.zero_add] using h.2.2.1

theorem term_code {n : ℕ} (L : ℕ) (t : Term n) (suffix : List Bool) (hlen : (t.code ++ suffix).length ≤ L) :
    termSize L (t.code ++ suffix) = t.size ∧ termRest L (t.code ++ suffix) = suffix := by
  have hn : t.size ≤ L := by have := t.size_le_code_length; rw [List.length_append] at hlen; omega
  have h := TermSpanCorrect.run_term L t hn [] suffix 0
  exact ⟨by simpa only [termSize, termResult, Nat.zero_add] using congrArg TermSpanControl.State.nodes h,
    by simpa only [termRest, termResult] using congrArg TermSpanControl.State.input h⟩

theorem formula_code {n : ℕ} (L : ℕ) (p : Formula n) (suffix : List Bool) (hlen : (p.code ++ suffix).length ≤ L) :
    formulaSize L (p.code ++ suffix) = formulaCount p := by
  have hn : SmallSyntaxForests.formulaTokens p ≤ L := by
    have := SmallSyntaxForests.formulaTokens_le_code_length p
    rw [List.length_append] at hlen
    omega
  have h := FormulaSpanCorrect.run_formula L p hn [] suffix 0
  simpa only [formulaSize, formulaResult, Nat.zero_add] using congrArg FormulaSpanControl.State.coordinates h

theorem pair_code {n : ℕ} (L : ℕ) (a b : Term n) (suffix : List Bool)
    (hlen : (a.code ++ b.code ++ suffix).length ≤ L) :
    termSize L (a.code ++ b.code ++ suffix) = a.size ∧
      termSize L (termRest L (a.code ++ b.code ++ suffix)) = b.size := by
  have hfirst := term_code L a (b.code ++ suffix) (by simpa only [List.append_assoc] using hlen)
  have hsecond := term_code L b suffix (by simp only [List.length_append] at hlen ⊢; omega)
  simpa only [List.append_assoc, hfirst.2] using And.intro hfirst.1 hsecond.1

end JointThermoComplexity.Complexity.PreorderLookahead

#print axioms JointThermoComplexity.Complexity.PreorderLookahead.term_code
#print axioms JointThermoComplexity.Complexity.PreorderLookahead.formula_code
#print axioms JointThermoComplexity.Complexity.PreorderLookahead.pair_code
