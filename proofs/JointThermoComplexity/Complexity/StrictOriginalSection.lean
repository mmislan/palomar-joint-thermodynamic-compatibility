module
public import proofs.JointThermoComplexity.Complexity.FiniteStrictPrefix
public import proofs.JointThermoComplexity.Complexity.FiniteRowEnergyLoop

set_option autoImplicit false
@[expose] public section

/-! Actual blank prefix followed by the entire bounded original-row traversal:
total polynomial runtime on raw inputs and exact finite energy bytes on Domain. -/

namespace JointThermoComplexity.Complexity.StrictOriginalSection
open _root_.Complexity _root_.Complexity.TM HeaderAt
open StrictInitialComposition (arity scratch sharedScale)
open StrictRowInitialization (rowPorts width)
open EquationSystemCodec FiniteStrictData

def rowBound (B W : ℕ) : ℕ := 42 * B ^ 3 + 8976 * B ^ 2 + 108 * B * W + 12077 * B + 2

theorem row_time_eq (B W : ℕ) : RowEnergyLoop.timeBound B W B = rowBound B W := by
  simp only [RowEnergyLoop.timeBound, RowEnergyStep.timeBound, RowReadSquareMachine.timeBound,
    EquationRowMachine.timeBound, MonomialPrefixMachine.timeBound, MarkedNaturalLoop.timeBound,
    RowSquareMachine.timeBound, RowPairSelect.timeBound, RowPairEntry.timeBound,
    EquationProductReplay.timeBound, SmallCoefficientMatch.timeBound, rowBound]
  ring

theorem rowBound_mono (B W V : ℕ) (h : W ≤ V) : rowBound B W ≤ rowBound B V := by
  unfold rowBound
  gcongr

def result (boxed : Bool) (input : List Bool) : RowEnergyControl.State :=
  RowEnergyControl.run (input.length + 2) (sharedScale input).bits (input.length + 2)
    (StrictLeadingFrame.rowState boxed input)

def machine (boxed : Bool) : TM 64 := seqTM (StrictLeadingFrame.machine boxed) (RowEnergyLoop.machine rowPorts 29)
def timeBound (L : ℕ) (boxed : Bool) : ℕ :=
  StrictLeadingFrame.timeBound L boxed + 1 + rowBound (L + 2) (width L L)

noncomputable def widthPolynomial : Polynomial ℕ :=
  4 * (Polynomial.X + 2) + Polynomial.X + StrictInitialComposition.scalePolynomial
noncomputable def rowPolynomial : Polynomial ℕ :=
  42 * (Polynomial.X + 2) ^ 3 + 8976 * (Polynomial.X + 2) ^ 2 +
    108 * (Polynomial.X + 2) * widthPolynomial + 12077 * (Polynomial.X + 2) + 2
noncomputable def timePolynomial (boxed : Bool) : Polynomial ℕ := StrictLeadingFrame.timePolynomial boxed + 1 + rowPolynomial

theorem rowPolynomial_eval (L : ℕ) : rowPolynomial.eval L = rowBound (L + 2) (width L L) := by
  simp [rowPolynomial, widthPolynomial, rowBound, width, StrictInitialComposition.scalePolynomial_eval]
  ring

theorem timePolynomial_eval (L : ℕ) (boxed : Bool) : (timePolynomial boxed).eval L = timeBound L boxed := by
  simp [timePolynomial, timeBound, StrictLeadingFrame.timePolynomial_eval, rowPolynomial_eval]

theorem source_suffix_bound (input : List Bool) : (HeaderControl.suffix input).length ≤ input.length := by
  have h := congrArg List.length (HeaderControl.consumed_and_suffix input)
  simp only [List.length_append] at h
  omega

theorem width_mono (L n : ℕ) (hn : n ≤ L) : width L n ≤ width L L := by
  unfold width
  omega

theorem hoareTime (boxed : Bool) (input : List Bool) :
    (machine boxed).HoareTime (StrictScheduleEntry.Initial input)
      (fun inp work out => RowEnergyStep.Logical rowPorts (result boxed input) (sharedScale input).bits
        (input.length + 2) (width input.length (arity input))
        (StrictLeadingInitialization.Extra input.length (arity input) (scratch input) input) inp work out ∧
        IsReg (input.length + 2) (work 29)) (timeBound input.length boxed) := by
  have hi := StrictLeadingFrame.hoareTime boxed input
  have hlen : (StrictLeadingFrame.rowState boxed input).row.input.length ≤ input.length + 2 :=
    (source_suffix_bound input).trans (by omega)
  have hr := RowEnergyLoop.hoareTime rowPorts (29 : Fin 64) (by decide) (by decide)
    (StrictLeadingFrame.rowState boxed input) (sharedScale input).bits (input.length + 2)
    (width input.length (arity input)) (input.length + 2) (by omega) hlen
    (StrictLeadingInitialization.Extra input.length (arity input) (scratch input) input)
    (StrictLeadingFrame.extra_stable _ _ _ _) (StrictLeadingFrame.extra_fuel_stable _ _ _ _)
  have hseq := seqTM_hoareTime _ _ hi (by
    rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    exact ⟨⟨hc, hr⟩, hf⟩) hr
  apply hseq.mono_bound
  rw [row_time_eq]
  have ht := rowBound_mono (input.length + 2) _ _
    (width_mono input.length (arity input) (HeaderControl.count_le_length input))
  unfold timeBound
  omega

def finiteState (p : Data) : EquationRowControl.State :=
  (StrictRowInitialization.state (SparseListCodec.unaryCode p.arity) ((rowsCodec p.arity).code p.rows) []).row

theorem encoded_hoareTime (boxed : Bool) (p : Data) (hp : FiniteEquationHardness.Domain p) :
    (machine boxed).HoareTime (StrictScheduleEntry.Initial (code p))
      (fun inp work out => Cursor (code p) []
        (SparseListCodec.unaryCode (variableCount p) ++
          (FiniteRowSquare.finiteEntries (FiniteStrictPrefix.lead boxed p) ++
            FiniteRowSquare.finiteEntries (FiniteRowEnergyLoop.energy p))) inp work out ∧
        (∀ j, Parked (work j)) ∧
        StrictLeadingInitialization.Extra (inputLength p) p.arity (scratch (code p)) (code p) work ∧
        IsReg (inputLength p + 2) (work 29))
      (timeBound (inputLength p) boxed) := by
  let emitted := SparseListCodec.unaryCode (variableCount p) ++
    FiniteRowSquare.finiteEntries (FiniteStrictPrefix.lead boxed p)
  have hi := FiniteStrictPrefix.hoareTime boxed p
  have hlen : ((rowsCodec p.arity).code p.rows ++ []).length ≤ inputLength p + 2 := by
    rw [List.append_nil]
    exact (FiniteStrictPrefix.row_length_bound p).trans (by omega)
  have hr := FiniteRowEnergyLoop.encoded_hoareTime rowPorts (29 : Fin 64) (by decide) (by decide)
    p hp (finiteState p) [] emitted (inputLength p + 2) (width (inputLength p) p.arity) (by omega) hlen
    (StrictLeadingInitialization.Extra (inputLength p) p.arity (scratch (code p)) (code p))
    (StrictLeadingFrame.extra_stable _ _ _ _) (StrictLeadingFrame.extra_fuel_stable _ _ _ _)
  have hseq := seqTM_hoareTime _ _ hi (by
    rintro inp work out ⟨⟨hc, hr⟩, hf⟩
    obtain ⟨hin, hw, ho⟩ := hc.phase
    rw [hin, hw, ho]
    simpa only [RowEnergyStep.Logical, finiteState, StrictRowInitialization.state, emitted, List.append_nil, scaleCount,
      Nat.add_assoc] using And.intro (And.intro hc hr) hf) hr
  apply hseq.consequence (fun _ _ _ h => h)
  · rintro inp work out ⟨hc, hr, hf⟩
    exact ⟨by simpa only [finiteState, StrictRowInitialization.state, code, emitted, List.append_assoc] using hc,
      hr.square.saved.safe, hr.square.saved.extra, hf⟩
  · rw [row_time_eq]
    have hn : p.arity ≤ inputLength p := by
      rw [← FiniteStrictPrefix.header_count]
      exact HeaderControl.count_le_length (code p)
    have ht := rowBound_mono (inputLength p + 2) _ _ (width_mono (inputLength p) p.arity hn)
    unfold timeBound
    omega

end JointThermoComplexity.Complexity.StrictOriginalSection

#print axioms JointThermoComplexity.Complexity.StrictOriginalSection.row_time_eq
#print axioms JointThermoComplexity.Complexity.StrictOriginalSection.timePolynomial_eval
#print axioms JointThermoComplexity.Complexity.StrictOriginalSection.hoareTime
#print axioms JointThermoComplexity.Complexity.StrictOriginalSection.encoded_hoareTime
