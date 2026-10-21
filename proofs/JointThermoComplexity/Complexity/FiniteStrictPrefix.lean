module
public import proofs.JointThermoComplexity.Complexity.StrictLeadingFrame
public import proofs.JointThermoComplexity.Complexity.FiniteGeneratedEnergy

set_option autoImplicit false
@[expose] public section

/-! Exact finite-source header, binder and leading bytes of the actual blank prefix machine. -/

namespace JointThermoComplexity.Complexity.FiniteStrictPrefix
open _root_.Complexity _root_.Complexity.TM EquationSystemCodec FiniteStrictData
open StrictInitialComposition (arity scratch)

theorem source_header (p : Data) : code p = RealSyntax.binderCode p.arity ++ (rowsCodec p.arity).code p.rows := by
  rw [code, UnaryBinderFramed.unaryCode_eq]
  rfl

theorem header_count (p : Data) : arity (code p) = p.arity := by
  rw [arity, source_header]
  exact HeaderControl.count_code _ _

theorem header_copied (p : Data) : HeaderControl.copied (code p) = SparseListCodec.unaryCode p.arity := by
  rw [source_header, HeaderControl.copied_code, UnaryBinderFramed.unaryCode_eq]
  rfl

theorem header_suffix (p : Data) : HeaderControl.suffix (code p) = (rowsCodec p.arity).code p.rows := by
  rw [source_header]
  exact HeaderControl.suffix_code _ _

theorem binder_count (p : Data) : StrictLeadingInitialization.binder (inputLength p) p.arity = variableCount p := by
  dsimp only [StrictLeadingInitialization.binder, StrictLeadingInitialization.leadAddress,
    variableCount, scaleCoordinateCount, scaleCount, thresholdCount]
  omega

theorem vector_assoc (n m k : ℕ) :
    (![ (n + m + 1) * 2 + k, 0] : Fin 2 → ℕ) = ![(n + (m + 1)) * 2 + k, 0] := by
  rw [Nat.add_assoc]

theorem raw_values (p : Data) : StrictLeadingInitialization.rawValues (inputLength p) p.arity =
    FiniteGeneratedEnergy.leadValues p := vector_assoc p.arity (scaleCount p) (thresholdCount p)

def lead (boxed : Bool) (p : Data) : SparseInteger.Poly (Fin (variableCount p)) :=
  if boxed then FiniteGeneratedEnergy.boxedLead p else FiniteGeneratedEnergy.unboxedLead p

theorem leading_entries (boxed : Bool) (p : Data) :
    RowSquareCanonical.entries (StrictGeneratedTemplates.data
      (StrictLeadingInitialization.rawValues (inputLength p) p.arity) (StrictLeadingInitialization.kind boxed)) =
      FiniteRowSquare.finiteEntries (lead boxed p) := by
  rw [raw_values]
  cases boxed with
  | false =>
    change RowSquareCanonical.entries (StrictGeneratedTemplates.data (FiniteGeneratedEnergy.leadValues p) .unboxedLead) = _
    rw [FiniteGeneratedEnergy.unboxed_lead_data]
    rfl
  | true =>
    change RowSquareCanonical.entries (StrictGeneratedTemplates.data (FiniteGeneratedEnergy.leadValues p) .boxedLead) = _
    rw [FiniteGeneratedEnergy.boxed_lead_data]
    rfl

theorem word_code (boxed : Bool) (p : Data) : StrictLeadingFrame.word boxed (code p) =
    SparseListCodec.unaryCode (variableCount p) ++ FiniteRowSquare.finiteEntries (lead boxed p) := by
  rw [StrictLeadingFrame.word, header_count]
  change SparseListCodec.unaryCode (StrictLeadingInitialization.binder (inputLength p) p.arity) ++ _ = _
  rw [binder_count]
  erw [leading_entries]

theorem row_length_bound (p : Data) : ((rowsCodec p.arity).code p.rows).length ≤ inputLength p := by
  simp only [inputLength, code, List.length_append]
  omega

theorem hoareTime (boxed : Bool) (p : Data) :
    (StrictLeadingFrame.machine boxed).HoareTime (StrictScheduleEntry.Initial (code p))
      (StrictLeadingInitialization.Framed (inputLength p) p.arity (SparseListCodec.unaryCode p.arity)
        ((rowsCodec p.arity).code p.rows)
        (SparseListCodec.unaryCode (variableCount p) ++ FiniteRowSquare.finiteEntries (lead boxed p))
        (StrictLeadingInitialization.Extra (inputLength p) p.arity (scratch (code p)) (code p)))
      (StrictLeadingFrame.timeBound (inputLength p) boxed) := by
  simpa only [header_count, header_copied, header_suffix, word_code, inputLength] using
    StrictLeadingFrame.hoareTime boxed (code p)

end JointThermoComplexity.Complexity.FiniteStrictPrefix

#print axioms JointThermoComplexity.Complexity.FiniteStrictPrefix.word_code
#print axioms JointThermoComplexity.Complexity.FiniteStrictPrefix.hoareTime
