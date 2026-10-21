module
public import proofs.JointThermoComplexity.Complexity.MotifCoreBlock

set_option autoImplicit false
@[expose] public section

/-! Appending the actual valid motif block completes the exact original total formula-map code. -/

namespace JointThermoComplexity.Complexity.MotifFormulaSuffix
open CircuitSerialization

def word (input : List Bool) : List Bool := match NetworkCodec.decode input with
  | none => []
  | some Q => (MotifCoreDenseCode.formula Q).code

theorem formula_eq_box_suffix (Q : NetworkCodec.Input) : MotifCoreDenseCode.formula Q = BoxSuffix.formula Q := rfl

theorem full_code (input : List Bool) :
    BoxFormulaEntry.code input ++ word input = (NetworkCodec.toSentence input).code := by
  cases hd : NetworkCodec.decode input with
  | none =>
    simp only [BoxFormulaEntry.code, ActivityFormulaEntry.code, CurrentFormulaEntry.code, NetworkCircuitEntry.code,
      FormulaStart.code, NetworkCircuitEntry.word, CurrentContinuationBranch.word, ActivityContinuationBranch.word,
      BoxContinuationBranch.word, word, NetworkCodec.toSentence, hd, FalseOutput.sentence, List.append_nil]
  | some Q =>
    have hcurrent : (NetworkCodec.toSentence input).code = CurrentFormulaEntry.code input ++
        (NetworkFormula.constraintsFormula Q.network (NetworkMembership.activityIndex Q.network)
          (NetworkMembership.currentIndex Q.network)).code := by
      simpa only [CurrentFormulaEntry.code, NetworkCircuitEntry.code, FormulaStart.code, NetworkCircuitEntry.word,
        CurrentContinuationBranch.word, NetworkCodec.toSentence, hd, FormulaPrefix.suffix,
        RealSyntax.Formula.code, conjunctionTag, List.append_assoc] using FormulaPrefix.sentence_code Q
    have hc : (NetworkCodec.toSentence input).code = ActivityFormulaEntry.code input ++ (ActivitySuffix.formula Q).code := by
      rw [hcurrent, ActivitySuffix.constraints_code]
      simp only [ActivityFormulaEntry.code, ActivityContinuationBranch.word, hd, List.append_assoc]
    rw [hc, BoxSuffix.activity_suffix_code]
    simp only [BoxFormulaEntry.code, BoxContinuationBranch.word, word, hd, formula_eq_box_suffix, List.append_assoc]

end JointThermoComplexity.Complexity.MotifFormulaSuffix

#print axioms JointThermoComplexity.Complexity.MotifFormulaSuffix.formula_eq_box_suffix
#print axioms JointThermoComplexity.Complexity.MotifFormulaSuffix.full_code
