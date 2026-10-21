module
public import proofs.JointThermoComplexity.Complexity.SignedRawControl
public import proofs.JointThermoComplexity.Complexity.SparseListCodec

set_option autoImplicit false
@[expose] public section

/-! Static-capacity control for marked binary reference lists. Overflow stops
after its marker, before another numeric field. Every finite raw input splits
exactly, and canonical lists of length at most the capacity are unchanged. -/

namespace JointThermoComplexity.Complexity.BoundedOccurrenceControl

structure Result where
  taken : List Bool
  rest : List Bool
  values : List ℕ
  marker : Bool
  available : Bool

def stop (input : List Bool) : Result :=
  ⟨BooleanMachine.copied input, BooleanMachine.suffix input, [],
    SourceBitRead.value input, BooleanMachine.accepted input⟩

def scan : ℕ → List Bool → Result
  | 0, input => stop input
  | capacity + 1, input =>
    if SourceBitRead.value input then
      let body := BooleanMachine.suffix input
      let field := NaturalRawControl.scan body
      let tail := scan capacity field.rest
      { tail with
        taken := BooleanMachine.copied input ++ field.taken ++ tail.taken
        values := NaturalCanonicalLoad.value body :: tail.values }
    else stop input

def closed (r : Result) : Bool := r.available && !r.marker

theorem split (capacity : ℕ) (input : List Bool) :
    (scan capacity input).taken ++ (scan capacity input).rest = input := by
  induction capacity generalizing input with
  | zero => exact BooleanMachine.consumed_and_suffix input
  | succ capacity ih =>
    simp only [scan]
    split
    · rw [List.append_assoc, List.append_assoc, ih, NaturalRawControl.split,
        BooleanMachine.consumed_and_suffix]
    · exact BooleanMachine.consumed_and_suffix input

theorem rest_length (capacity : ℕ) (input : List Bool) :
    (scan capacity input).rest.length ≤ input.length := by
  have h := congrArg List.length (split capacity input)
  simp only [List.length_append] at h
  omega

theorem values_length (capacity : ℕ) (input : List Bool) :
    (scan capacity input).values.length ≤ capacity := by
  induction capacity generalizing input with
  | zero => simp [scan, stop]
  | succ capacity ih =>
    simp only [scan]
    split
    · simpa only [List.length_cons] using Nat.succ_le_succ (ih _)
    · simp [stop]

theorem bits_length (capacity : ℕ) (input : List Bool) :
    ∀ v ∈ (scan capacity input).values, v.bits.length ≤ input.length := by
  induction capacity generalizing input with
  | zero => simp [scan, stop]
  | succ capacity ih =>
    simp only [scan]
    split
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact (NaturalCanonicalLoad.bits_length _).trans (SignedRawControl.suffix_length input)
      · have hn := congrArg List.length (NaturalRawControl.split (BooleanMachine.suffix input))
        simp only [List.length_append] at hn
        have hs := SignedRawControl.suffix_length input
        exact (ih _ v hv).trans (by omega)
    · simp [stop]

theorem finite_code {n : ℕ} (vs : List (Fin n)) (suffix : List Bool) (capacity : ℕ)
    (hlen : vs.length ≤ capacity) :
    scan capacity (SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) =
      ⟨SparseListCodec.listCode (SparseListCodec.finite n) vs, suffix, vs.map Fin.val, false, true⟩ := by
  induction vs generalizing capacity with
  | nil => cases capacity <;> rfl
  | cons v vs ih =>
    cases capacity with
    | zero => simp at hlen
    | succ capacity =>
      have ht := ih capacity (by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hlen)
      simp [scan, SparseListCodec.listCode, SparseListCodec.finite, SourceBitRead.value,
        BooleanMachine.copied, BooleanMachine.suffix, NaturalRawControl.natural,
        NaturalCanonicalLoad.value, List.append_assoc] at ht ⊢
      rw [ht]
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end JointThermoComplexity.Complexity.BoundedOccurrenceControl

#print axioms JointThermoComplexity.Complexity.BoundedOccurrenceControl.split
#print axioms JointThermoComplexity.Complexity.BoundedOccurrenceControl.bits_length
#print axioms JointThermoComplexity.Complexity.BoundedOccurrenceControl.finite_code
