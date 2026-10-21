module
public import proofs.JointThermoComplexity.Complexity.RecordControl
public import proofs.JointThermoComplexity.Complexity.DimensionEntry

set_option autoImplicit false
@[expose] public section

/-! Header, record and end-of-input status agree with the total network decoder. -/

namespace JointThermoComplexity.Complexity.NetworkInputControl
open DimensionHeaders

def records (input : List Bool) := RecordControl.network (species input) (reactions input) (cores input)

def accepted (input : List Bool) : Bool :=
  (DimensionHeaders.accepted input && (records input).valid (tail₃ input)) &&
    ((records input).rest (tail₃ input)).isEmpty

def copied (input : List Bool) : List Bool :=
  DimensionEntry.consumed input ++ (records input).taken (tail₃ input)

def rest (input : List Bool) : List Bool := (records input).rest (tail₃ input)

theorem consumed_split (input : List Bool) : copied input ++ rest input = input := by
  simp only [copied, rest, List.append_assoc, (records input).split]
  exact DimensionHeaders.prefix_and_suffix input

theorem parseInput_eq (input : List Bool) :
    NetworkCodec.parseInput input = if DimensionHeaders.accepted input then
      do
        let (Q, suffix) ← (DataCodec.network (species input) (reactions input) (cores input)).parse (tail₃ input)
        pure (⟨species input, reactions input, cores input, Q⟩, suffix)
    else none := by
  cases h₀ : HeaderControl.valid input <;>
    cases h₁ : HeaderControl.valid (tail₁ input) <;> cases h₂ : HeaderControl.valid (tail₂ input) <;>
    simp_all [NetworkCodec.parseInput, NetworkCodec.dimension, HeaderControl.parseBinders_eq,
      DimensionHeaders.accepted, species, reactions, cores, tail₁, tail₂, tail₃]

theorem status_iff_decode (input : List Bool) :
    accepted input = true ↔ ∃ Q, NetworkCodec.decode input = some Q := by
  cases hh : DimensionHeaders.accepted input with
  | false => simp [accepted, NetworkCodec.decode, parseInput_eq, hh]
  | true =>
    cases hp : (DataCodec.network (species input) (reactions input) (cores input)).parse (tail₃ input) with
    | none =>
      have hv : (records input).valid (tail₃ input) ≠ true := by
        intro h
        obtain ⟨Q, suffix, hparse⟩ := (records input).accepts (tail₃ input) |>.mp h
        simp [hp] at hparse
      simp [accepted, hh, hv, NetworkCodec.decode, parseInput_eq, hp]
    | some pair =>
      obtain ⟨Q, suffix⟩ := pair
      have hv : (records input).valid (tail₃ input) = true :=
        (records input).accepts (tail₃ input) |>.mpr ⟨Q, suffix, hp⟩
      have hr : (records input).rest (tail₃ input) = suffix := ((records input).parsed hp).2
      by_cases hs : suffix = []
      · simp [accepted, hh, hv, hr, hs, NetworkCodec.decode, parseInput_eq, hp]
      · simp [accepted, hh, hv, hr, hs, NetworkCodec.decode, parseInput_eq, hp]

theorem accepted_copies_input (input : List Bool) (h : accepted input = true) : copied input = input := by
  have hr : rest input = [] := by
    simp only [accepted, Bool.and_eq_true] at h
    exact List.isEmpty_iff.mp h.2
  simpa only [hr, List.append_nil] using consumed_split input

end JointThermoComplexity.Complexity.NetworkInputControl

#print axioms JointThermoComplexity.Complexity.NetworkInputControl.status_iff_decode
#print axioms JointThermoComplexity.Complexity.NetworkInputControl.accepted_copies_input
