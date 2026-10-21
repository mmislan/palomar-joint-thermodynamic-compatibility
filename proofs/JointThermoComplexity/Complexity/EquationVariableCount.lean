module
public import proofs.JointThermoComplexity.Complexity.CompleteEquationFP

set_option autoImplicit false
@[expose] public section

/-! The actual output binder is the positive canonical finite variable count, with exact normalized row bytes. -/

namespace JointThermoComplexity.Complexity.EquationVariableCount
open RealSyntax SourceCoordinateEnumeration

theorem canonical_count (s : Sentence) :
    EquationLoopInitialization.variableCount s.code = sourceCount s := by
  have ha : HeaderControl.count s.code = s.arity := by simp only [Sentence.code, HeaderControl.count_code]
  have hs : HeaderControl.suffix s.code = s.formula.code := by simp only [Sentence.code, HeaderControl.suffix_code]
  have hlen : s.formula.code.length ≤ s.code.length := by
    simp only [Sentence.code, List.length_append]
    omega
  have hformula := PreorderLookahead.formula_code s.code.length s.formula [] (by simpa only [List.append_nil] using hlen)
  change HeaderControl.count s.code + PreorderLookahead.formulaSize s.code.length (HeaderControl.suffix s.code) = _
  rw [ha, hs]
  simpa only [List.append_nil, sourceCount] using congrArg (fun v => s.arity + v) hformula

theorem formulaCount_pos {n : ℕ} (p : Formula n) : 0 < formulaCount p := by
  cases p <;> dsimp [formulaCount] <;> omega

theorem sourceCount_pos (s : Sentence) : 0 < sourceCount s := by
  have h := formulaCount_pos s.formula
  dsimp [sourceCount]
  omega

def count (input : List Bool) : ℕ := sourceCount (SourceSmallLiterals.normalizeSmall input)

theorem normalized_count (input : List Bool) :
    EquationLoopInitialization.variableCount (SmallSyntaxFP.code input) = count input :=
  canonical_count (SourceSmallLiterals.normalizeSmall input)

theorem count_pos (input : List Bool) : 0 < count input := sourceCount_pos _

theorem count_bound (input : List Bool) : count input ≤ 55 * (input.length + 4) := by
  have hc := sourceCount_le_code_length (SourceSmallLiterals.normalizeSmall input)
  have hl := SmallSyntaxFP.output_length input
  change count input ≤ 5 * (SmallSyntaxFP.code input).length at hc
  omega

theorem raw_sentence_code (s : Sentence) (hh : s.formula.literalHeight ≤ 2) :
    CompleteEquationMachine.code s.code = RealSyntax.binderCode (sourceCount s) ++
      PreorderRowCode.numericRows (PreorderSourceEquations.equations s) := by
  rw [CompleteEquationMachine.code, canonical_count, PreorderRowCode.code,
    PreorderFormulaEmission.rows_sentence s hh, PreorderRowCode.rows_words]

theorem normalized_code (input : List Bool) :
    CompleteEquationFP.code input = RealSyntax.binderCode (count input) ++
      PreorderRowCode.numericRows (PreorderSourceEquations.normalized input) := by
  change RealSyntax.binderCode (EquationLoopInitialization.variableCount (SmallSyntaxFP.code input)) ++
    PreorderRowCode.normalized input = _
  rw [normalized_count, PreorderRowCode.normalized_eq]

end JointThermoComplexity.Complexity.EquationVariableCount

#print axioms JointThermoComplexity.Complexity.EquationVariableCount.canonical_count
#print axioms JointThermoComplexity.Complexity.EquationVariableCount.normalized_code
