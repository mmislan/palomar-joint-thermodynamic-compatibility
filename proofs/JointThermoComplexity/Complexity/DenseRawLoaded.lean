module
public import proofs.JointThermoComplexity.Complexity.DenseTemplatePacket

set_option autoImplicit false
@[expose] public section

/-! Closed raw occurrence scans yield canonical present reference registers,
even when source numeric fields are malformed or outside the declared arity. -/

namespace JointThermoComplexity.Complexity.DenseRawLoaded
open _root_.Complexity _root_.Complexity.TM
open BoundedOccurrenceMachine
variable {w : ℕ}

theorem encoded (slots : List (Port w)) (ending flag : Fin (w + 1)) (input : List Bool) (work : Fin (w + 1) → Tape)
    (hm : (BoundedOccurrenceControl.scan slots.length input).marker = false) (h : Loaded slots ending flag input work) :
    BoundedOccurrenceRun.Encoded slots ending (BoundedOccurrenceControl.scan slots.length input).values work := by
  induction slots generalizing input with
  | nil =>
    change SourceBitRead.value input = false at hm
    change (work ending).read = Γ.zero
    rw [h.1, hm]
    rfl
  | cons p slots ih =>
    cases hv : SourceBitRead.value input with
    | false =>
      simpa only [List.length_cons, BoundedOccurrenceControl.scan, hv, Bool.false_eq_true, ↓reduceIte,
        BoundedOccurrenceControl.stop, BoundedOccurrenceRun.Encoded, Γ.ofBool] using h.1
    | true =>
      have hc : BinaryIncrementRun.Register (NaturalCanonicalLoad.value (BooleanMachine.suffix input)) (work p.1) ∧
          Loaded slots ending flag (NaturalRawControl.scan (BooleanMachine.suffix input)).rest work := by
        simpa only [hv, ↓reduceIte] using h.2
      have htail : (BoundedOccurrenceControl.scan slots.length
          (NaturalRawControl.scan (BooleanMachine.suffix input)).rest).marker = false := by
        simpa only [List.length_cons, BoundedOccurrenceControl.scan, hv, ↓reduceIte] using hm
      have ht := ih _ htail hc.2
      simp only [List.length_cons, BoundedOccurrenceControl.scan, hv, ↓reduceIte, BoundedOccurrenceRun.Encoded]
      exact ⟨by simpa only [hv, Γ.ofBool] using h.1, hc.1, ht⟩

theorem choice_data (capacity : ℕ) (input : List Bool) (m : ℕ)
    (h : OccurrenceDispatchControl.choice capacity input = some m) :
    (BoundedOccurrenceControl.scan capacity input).marker = false ∧
      m = (BoundedOccurrenceControl.scan capacity input).values.length := by
  cases hc : BoundedOccurrenceControl.closed (BoundedOccurrenceControl.scan capacity input) with
  | false =>
    simp only [OccurrenceDispatchControl.choice, hc, Bool.false_eq_true, ↓reduceIte] at h
    cases h
  | true =>
    have hv : (BoundedOccurrenceControl.scan capacity input).values.length = m := Option.some.inj (by
      simpa only [OccurrenceDispatchControl.choice, hc, ↓reduceIte] using h)
    have hm : (BoundedOccurrenceControl.scan capacity input).marker = false := by
      cases hmark : (BoundedOccurrenceControl.scan capacity input).marker with
      | false => rfl
      | true =>
        simp only [BoundedOccurrenceControl.closed, hmark, Bool.not_true, Bool.and_false] at hc
        cases hc
    exact ⟨hm, hv.symm⟩

theorem encoded_of_choice (slots : List (Port w)) (ending flag : Fin (w + 1)) (input : List Bool)
    (work : Fin (w + 1) → Tape) (m : ℕ) (hchoice : OccurrenceDispatchControl.choice slots.length input = some m)
    (h : Loaded slots ending flag input work) :
    BoundedOccurrenceRun.Encoded slots ending (BoundedOccurrenceControl.scan slots.length input).values work :=
  encoded slots ending flag input work (choice_data slots.length input m hchoice).1 h

end JointThermoComplexity.Complexity.DenseRawLoaded

#print axioms JointThermoComplexity.Complexity.DenseRawLoaded.encoded
#print axioms JointThermoComplexity.Complexity.DenseRawLoaded.encoded_of_choice
