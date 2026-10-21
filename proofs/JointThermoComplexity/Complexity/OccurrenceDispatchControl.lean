module
public import proofs.JointThermoComplexity.Complexity.BoundedOccurrenceRun

set_option autoImplicit false
@[expose] public section

/-! Recover the finite occurrence count from the retained markers. Missing
input and capacity overflow route to the invalid alternative. -/

namespace JointThermoComplexity.Complexity.OccurrenceDispatchControl
open _root_.Complexity _root_.Complexity.TM
open BoundedOccurrenceMachine
variable {w : ℕ}

def Position : List (Port w) → Fin (w + 1) → ℕ → (Fin (w + 1) → Tape) → Prop
  | [], ending, 0, work => (work ending).read = Γ.zero
  | p :: _, _, 0, work => (work p.2).read = Γ.zero
  | [], _, _ + 1, _ => False
  | p :: slots, ending, m + 1, work => (work p.2).read = Γ.one ∧ Position slots ending m work

def Overflow : List (Port w) → Fin (w + 1) → (Fin (w + 1) → Tape) → Prop
  | [], ending, work => (work ending).read = Γ.one
  | p :: slots, ending, work => (work p.2).read = Γ.one ∧ Overflow slots ending work

def choice (capacity : ℕ) (input : List Bool) : Option ℕ :=
  let r := BoundedOccurrenceControl.scan capacity input
  if BoundedOccurrenceControl.closed r then some r.values.length else none

def Route (slots : List (Port w)) (ending flag : Fin (w + 1)) : Option ℕ → (Fin (w + 1) → Tape) → Prop
  | none, work => (work flag).read ≠ Γ.one ∨ Overflow slots ending work
  | some m, work => (work flag).read = Γ.one ∧ Position slots ending m work

theorem loaded_shape (slots : List (Port w)) (ending flag : Fin (w + 1))
    (input : List Bool) (work : Fin (w + 1) → Tape) (h : Loaded slots ending flag input work) :
    if (BoundedOccurrenceControl.scan slots.length input).marker then Overflow slots ending work
    else Position slots ending (BoundedOccurrenceControl.scan slots.length input).values.length work := by
  induction slots generalizing input with
  | nil =>
    cases hv : SourceBitRead.value input <;>
      simpa only [List.length_nil, BoundedOccurrenceControl.scan, BoundedOccurrenceControl.stop,
        hv, Bool.false_eq_true, ↓reduceIte, List.length_nil, Position, Overflow, Γ.ofBool] using h.1
  | cons p slots ih =>
    cases hv : SourceBitRead.value input with
    | false =>
      simpa only [List.length_cons, BoundedOccurrenceControl.scan, BoundedOccurrenceControl.stop,
        hv, Bool.false_eq_true, ↓reduceIte, List.length_nil, Position, Γ.ofBool] using h.1
    | true =>
      have hc : BinaryIncrementRun.Register (NaturalCanonicalLoad.value (BooleanMachine.suffix input)) (work p.1) ∧
          Loaded slots ending flag (NaturalRawControl.scan (BooleanMachine.suffix input)).rest work := by
        simpa only [hv, ↓reduceIte] using h.2
      have hm : (work p.2).read = Γ.one := by simpa only [hv, Γ.ofBool] using h.1
      have ht := ih _ hc.2
      simp only [List.length_cons, BoundedOccurrenceControl.scan, hv, ↓reduceIte]
      cases he : (BoundedOccurrenceControl.scan slots.length
        (NaturalRawControl.scan (BooleanMachine.suffix input)).rest).marker <;>
        simp only [he, Bool.false_eq_true, ↓reduceIte, Position, Overflow] at ht ⊢
      all_goals exact ⟨hm, ht⟩

theorem loaded_route (slots : List (Port w)) (ending flag : Fin (w + 1))
    (input : List Bool) (work : Fin (w + 1) → Tape) (h : Loaded slots ending flag input work) :
    Route slots ending flag (choice slots.length input) work := by
  have ha := BoundedOccurrenceRun.loaded_available slots ending flag input work h
  have hs := loaded_shape slots ending flag input work h
  cases hav : (BoundedOccurrenceControl.scan slots.length input).available with
  | false =>
    have hf : (work flag).read ≠ Γ.one := by rw [ha, hav]; decide
    simpa only [choice, BoundedOccurrenceControl.closed, hav, Bool.false_and,
      Bool.false_eq_true, ↓reduceIte, Route] using Or.inl hf
  | true =>
    have hf : (work flag).read = Γ.one := by rw [ha, hav]; rfl
    cases hm : (BoundedOccurrenceControl.scan slots.length input).marker with
    | false =>
      have hp : Position slots ending (BoundedOccurrenceControl.scan slots.length input).values.length work := by
        simpa only [hm, Bool.false_eq_true, ↓reduceIte] using hs
      simpa only [choice, BoundedOccurrenceControl.closed, hav, hm, Bool.not_false,
        Bool.true_and, ↓reduceIte, Route] using And.intro hf hp
    | true =>
      have ho : Overflow slots ending work := by simpa only [hm, ↓reduceIte] using hs
      simpa only [choice, BoundedOccurrenceControl.closed, hav, hm, Bool.not_true,
        Bool.true_and, Bool.false_eq_true, ↓reduceIte, Route] using Or.inr ho

theorem encoded_position (slots : List (Port w)) (ending : Fin (w + 1))
    (vs : List ℕ) (work : Fin (w + 1) → Tape) (h : BoundedOccurrenceRun.Encoded slots ending vs work) :
    Position slots ending vs.length work := by
  induction slots generalizing vs with
  | nil => cases vs with
    | nil => exact h
    | cons v vs => exact h.elim
  | cons p slots ih => cases vs with
    | nil => exact h
    | cons v vs => exact ⟨h.1, ih vs h.2.2⟩

theorem choice_code {n : ℕ} (vs : List (Fin n)) (suffix : List Bool) (capacity : ℕ)
    (hlen : vs.length ≤ capacity) :
    choice capacity (SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) = some vs.length := by
  simp only [choice, BoundedOccurrenceControl.finite_code vs suffix capacity hlen,
    BoundedOccurrenceControl.closed, Bool.not_false, Bool.true_and, ↓reduceIte, List.length_map]

end JointThermoComplexity.Complexity.OccurrenceDispatchControl

#print axioms JointThermoComplexity.Complexity.OccurrenceDispatchControl.loaded_route
#print axioms JointThermoComplexity.Complexity.OccurrenceDispatchControl.choice_code
