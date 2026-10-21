module
public import proofs.JointThermoComplexity.Complexity.SourceFormulaEOF
public import proofs.JointThermoComplexity.Complexity.RealFormulaParseSound

set_option autoImplicit false
@[expose] public section

/-! The actual parser control for a unary binder header and one complete formula matches sentence decoding. -/

namespace JointThermoComplexity.Complexity.SourceBinderControl
open RealSyntax

def initialState (input : List Bool) : SourceTermLoopState.State :=
  ⟨HeaderControl.copied input, HeaderControl.suffix input, 1, HeaderControl.valid input⟩

def finalState (L : ℕ) (input : List Bool) : SourceTermLoopState.State :=
  SourceFormulaEOF.finalState (HeaderControl.count input) L L (initialState input)

theorem input_bounds (L : ℕ) (input : List Bool) (hlen : input.length ≤ L) :
    HeaderControl.count input ≤ L ∧ (HeaderControl.count input).bits.length ≤ L ∧
    (HeaderControl.suffix input).length ≤ L ∧ (HeaderControl.copied input).length ≤ L := by
  have hcount := HeaderControl.count_le_length input
  have hbits := BinaryIncrementControl.bits_length_le (HeaderControl.count input)
  have hcopied := HeaderControl.copied_length_le input
  have hsplit := congrArg List.length (HeaderControl.consumed_and_suffix input)
  rw [List.length_append] at hsplit
  omega

theorem status_criterion (L : ℕ) (input : List Bool) (hlen : input.length ≤ L) :
    (finalState L input).valid = true ↔ ∃ s : Sentence, input = s.code := by
  constructor
  · intro h
    cases hv : HeaderControl.valid input with
    | false =>
      have hf : (finalState L input).valid = false := by
        simp only [finalState, initialState, hv, SourceFormulaEOF.initial_false]
      rw [hf] at h
      contradiction
    | true =>
      have hf : (SourceFormulaEOF.finalState (HeaderControl.count input) L L
          ⟨HeaderControl.copied input, HeaderControl.suffix input, 1, true⟩).valid = true := by
        simpa only [finalState, initialState, hv] using h
      obtain ⟨p, hp⟩ := (SourceFormulaEOF.status_criterion (HeaderControl.count input) L
        (HeaderControl.copied input) (HeaderControl.suffix input) (input_bounds L input hlen).2.2.1).mp hf
      refine ⟨⟨HeaderControl.count input, p⟩, ?_⟩
      change input = binderCode (HeaderControl.count input) ++ p.code
      rw [← HeaderControl.valid_copied_code input hv, ← hp]
      exact (HeaderControl.consumed_and_suffix input).symm
  · rintro ⟨s, rfl⟩
    rcases s with ⟨arity, p⟩
    have hlen' : p.code.length ≤ L := by
      change (binderCode arity ++ p.code).length ≤ L at hlen
      rw [List.length_append] at hlen
      omega
    have hp := (SourceFormulaEOF.status_criterion arity L (binderCode arity) p.code hlen').mpr ⟨p, rfl⟩
    simpa only [finalState, initialState, Sentence.code, HeaderControl.count_code, HeaderControl.copied_code,
      HeaderControl.suffix_code, HeaderControl.valid_code] using hp

theorem decode_criterion (L : ℕ) (input : List Bool) (hlen : input.length ≤ L) :
    (finalState L input).valid = true ↔ (decodeSentence input).isSome = true := by
  rw [status_criterion L input hlen]
  cases hd : decodeSentence input with
  | none =>
    constructor
    · rintro ⟨s, hs⟩
      have he := (decodeSentence_some_iff input s).mpr hs
      rw [hd] at he
      contradiction
    · intro h
      contradiction
  | some s =>
    exact ⟨fun _ => rfl, fun _ => ⟨s, decodeSentence_sound hd⟩⟩

end JointThermoComplexity.Complexity.SourceBinderControl

#print axioms JointThermoComplexity.Complexity.SourceBinderControl.status_criterion
#print axioms JointThermoComplexity.Complexity.SourceBinderControl.decode_criterion
