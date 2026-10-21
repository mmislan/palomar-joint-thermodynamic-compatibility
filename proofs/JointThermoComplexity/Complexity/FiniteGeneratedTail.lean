module
public import proofs.JointThermoComplexity.Complexity.StrictGeneratedTail
public import proofs.JointThermoComplexity.Complexity.FiniteGeneratedLoopData
public import proofs.JointThermoComplexity.Complexity.FiniteStrictPrefix

set_option autoImplicit false
@[expose] public section

/-! Exact finite scale/circle/error bytes of the actual generated tail and full strict codec. -/

namespace JointThermoComplexity.Complexity.FiniteGeneratedTail
open EquationSystemCodec FiniteStrictData
open StrictGeneratedTemplates GeneratedEnergyLoop

theorem coordinate_assoc (n m : ℕ) : n + m + 1 = n + (m + 1) := by omega

theorem coordinates_eq (p : Data) : GeneratedTailSetup.C (inputLength p) p.arity = scaleCoordinateCount p :=
  coordinate_assoc p.arity (scaleCount p)

theorem error_offset_eq (p : Data) : GeneratedTailSetup.D (inputLength p) p.arity = scaleCoordinateCount p * 2 :=
  congrArg (fun n => n * 2) (coordinates_eq p)

theorem scale_values (p : Data) : GeneratedTailSetup.scaleValues p.arity = FiniteGeneratedLoopData.scaleValues p := rfl

theorem error_values (p : Data) : GeneratedTailSetup.errorValues (inputLength p) p.arity =
    FiniteGeneratedLoopData.errorValues p := congrArg (fun n => (![n, n + 1] : Fin 2 → ℕ)) (error_offset_eq p)

theorem scale_word (p : Data) : GeneratedTailSetup.scaleWord (inputLength p) p.arity =
    FiniteRowSquare.finiteEntries (FiniteStrictSections.scaleEnergy p) := by
  change RowSquareCanonical.entries (data (FiniteGeneratedLoopData.scaleValues p) .scaleInitial) ++
    entries (FiniteGeneratedLoopData.scaleValues p) .scaleEdge (scaleCount p) = _
  have hi := congrArg RowSquareCanonical.entries (FiniteGeneratedLoopData.scale_initial_data p)
  rw [FiniteStrictSections.scaleEnergy, FiniteRowEnergyLoop.finiteEntries_append, FiniteGeneratedLoopData.scale_entries, hi]
  rfl

theorem circle_word (p : Data) : GeneratedTailSetup.circleWord (inputLength p) p.arity =
    FiniteRowSquare.finiteEntries (FiniteStrictSections.circleEnergy p) := by
  unfold GeneratedTailSetup.circleWord
  rw [coordinates_eq]
  exact FiniteGeneratedLoopData.circle_entries p

theorem error_word (p : Data) : GeneratedTailSetup.errorWord (inputLength p) p.arity =
    FiniteRowSquare.finiteEntries (FiniteStrictSections.errorEnergy p) := by
  unfold GeneratedTailSetup.errorWord
  rw [error_values]
  change RowSquareCanonical.entries (data (FiniteGeneratedLoopData.errorValues p) .errorInitial) ++
    entries (FiniteGeneratedLoopData.errorValues p) .errorEdge (thresholdCount p) = _
  have hi := congrArg RowSquareCanonical.entries (FiniteGeneratedLoopData.error_initial_data p)
  rw [FiniteStrictSections.errorEnergy, FiniteRowEnergyLoop.finiteEntries_append, FiniteGeneratedLoopData.error_entries, hi]
  rfl

theorem tail_word (p : Data) : StrictGeneratedTail.word (inputLength p) p.arity =
    FiniteRowSquare.finiteEntries (FiniteStrictSections.scaleEnergy p) ++
      FiniteRowSquare.finiteEntries (FiniteStrictSections.circleEnergy p) ++
      FiniteRowSquare.finiteEntries (FiniteStrictSections.errorEnergy p) ++ [false] := by
  rw [StrictGeneratedTail.word, scale_word, circle_word, error_word]

def targetCode (boxed : Bool) (p : Data) : List Bool := if boxed then boundedCode p else allRealCode p

theorem code_assembly (boxed : Bool) (p : Data) :
    (SparseListCodec.unaryCode (variableCount p) ++
      (FiniteRowSquare.finiteEntries (FiniteStrictPrefix.lead boxed p) ++
        FiniteRowSquare.finiteEntries (FiniteRowEnergyLoop.energy p))) ++
        StrictGeneratedTail.word (inputLength p) p.arity = targetCode boxed p := by
  cases boxed
  · simp only [targetCode, Bool.false_eq_true, ↓reduceIte, FiniteStrictPrefix.lead,
      FiniteStrictSections.allReal_code, tail_word, List.append_assoc]
  · simp only [targetCode, ↓reduceIte, FiniteStrictPrefix.lead,
      FiniteStrictSections.bounded_code, tail_word, List.append_assoc]

end JointThermoComplexity.Complexity.FiniteGeneratedTail

#print axioms JointThermoComplexity.Complexity.FiniteGeneratedTail.tail_word
#print axioms JointThermoComplexity.Complexity.FiniteGeneratedTail.code_assembly
