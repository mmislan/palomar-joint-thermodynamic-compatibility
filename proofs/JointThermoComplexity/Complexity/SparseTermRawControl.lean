module
public import proofs.JointThermoComplexity.Complexity.BoundedOccurrenceControl

set_option autoImplicit false
@[expose] public section

/-! One sparse term: signed coefficient followed by a statically bounded
marked occurrence list. Numeric magnitudes are always kept in binary. -/

namespace JointThermoComplexity.Complexity.SparseTermRawControl

def occurrences (capacity : ℕ) (input : List Bool) : BoundedOccurrenceControl.Result :=
  BoundedOccurrenceControl.scan capacity (SignedRawControl.rest input)

def taken (capacity : ℕ) (input : List Bool) : List Bool :=
  SignedRawControl.taken input ++ (occurrences capacity input).taken

def rest (capacity : ℕ) (input : List Bool) : List Bool := (occurrences capacity input).rest

theorem split (capacity : ℕ) (input : List Bool) : taken capacity input ++ rest capacity input = input := by
  rw [taken, rest, List.append_assoc, occurrences, BoundedOccurrenceControl.split, SignedRawControl.split]

theorem rest_length (capacity : ℕ) (input : List Bool) : (rest capacity input).length ≤ input.length := by
  have h := congrArg List.length (split capacity input)
  simp only [List.length_append] at h
  omega

theorem occurrence_count (capacity : ℕ) (input : List Bool) :
    (occurrences capacity input).values.length ≤ capacity := BoundedOccurrenceControl.values_length _ _

theorem occurrence_bits (capacity : ℕ) (input : List Bool) :
    ∀ v ∈ (occurrences capacity input).values, v.bits.length ≤ input.length := by
  intro v hv
  exact (BoundedOccurrenceControl.bits_length _ _ v hv).trans (SignedRawControl.rest_length input)

theorem occurrences_code {n : ℕ} (c : ℤ) (vs : List (Fin n)) (suffix : List Bool)
    (capacity : ℕ) (hlen : vs.length ≤ capacity) :
    occurrences capacity (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) =
      ⟨SparseListCodec.listCode (SparseListCodec.finite n) vs, suffix, vs.map Fin.val, false, true⟩ := by
  rw [occurrences, List.append_assoc, SignedRawControl.rest_integer]
  exact BoundedOccurrenceControl.finite_code vs suffix capacity hlen

theorem taken_code {n : ℕ} (c : ℤ) (vs : List (Fin n)) (suffix : List Bool)
    (capacity : ℕ) (hlen : vs.length ≤ capacity) :
    taken capacity (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) =
      BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs := by
  rw [taken, occurrences_code c vs suffix capacity hlen, List.append_assoc, SignedRawControl.taken_integer]

theorem rest_code {n : ℕ} (c : ℤ) (vs : List (Fin n)) (suffix : List Bool)
    (capacity : ℕ) (hlen : vs.length ≤ capacity) :
    rest capacity (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) = suffix := by
  rw [rest, occurrences_code c vs suffix capacity hlen]

end JointThermoComplexity.Complexity.SparseTermRawControl

#print axioms JointThermoComplexity.Complexity.SparseTermRawControl.split
#print axioms JointThermoComplexity.Complexity.SparseTermRawControl.occurrence_bits
#print axioms JointThermoComplexity.Complexity.SparseTermRawControl.occurrences_code
