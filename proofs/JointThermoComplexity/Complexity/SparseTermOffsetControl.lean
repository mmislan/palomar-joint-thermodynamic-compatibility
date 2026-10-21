module
public import proofs.JointThermoComplexity.Complexity.OffsetTemplateDispatch
public import proofs.JointThermoComplexity.Complexity.SparseTermRawControl

set_option autoImplicit false
@[expose] public section

/-! Pure all-raw control for one sparse term and its offset/count updates.
Canonical source terms agree with the exact raw normalization weights. -/

namespace JointThermoComplexity.Complexity.SparseTermOffsetControl

def taken (input : List Bool) : List Bool := SparseTermRawControl.taken 4 input
def rest (input : List Bool) : List Bool := SparseTermRawControl.rest 4 input
def choice (input : List Bool) : Option ℕ := OccurrenceDispatchControl.choice 4 (SignedRawControl.rest input)
def delta (boxed : Bool) (input : List Bool) : ℕ :=
  OffsetTemplateDispatch.added boxed (SignedRawControl.negative input) (SignedRawControl.magnitude input) (choice input)
def count (input : List Bool) : ℕ := match choice input with
  | none => 0
  | some m => 2 ^ m

theorem split (input : List Bool) : taken input ++ rest input = input := SparseTermRawControl.split 4 input
theorem rest_length (input : List Bool) : (rest input).length ≤ input.length := SparseTermRawControl.rest_length 4 input

theorem choice_le (input : List Bool) (m : ℕ) (h : choice input = some m) : m ≤ 4 :=
  OffsetTemplateDispatch.choice_le 4 (SignedRawControl.rest input) m h

theorem count_le (input : List Bool) : count input ≤ 16 := by
  cases h : choice input with
  | none => simp only [count, h]; omega
  | some m =>
    simpa only [count, h] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) (choice_le input m h)

theorem result_bits (boxed : Bool) (input : List Bool) (A : ℕ) :
    (A + delta boxed input).bits.length ≤ A.bits.length + 16 * (input.length + 2609) := by
  cases h : choice input with
  | none =>
    simp only [delta, h, OffsetTemplateDispatch.added, Nat.add_zero]
    omega
  | some m =>
    have hm := choice_le input m h
    have hp := OffsetTemplateProgram.bits_result (OffsetTemplateData.template boxed m)
      (SignedRawControl.negative input) (SignedRawControl.magnitude input) A (OffsetTemplateData.template_bounded boxed m hm)
    have hn := OffsetTemplateData.template_length boxed m hm
    have hb := SignedRawControl.magnitude_bits_length input
    have hbound := Nat.mul_le_mul hn (Nat.add_le_add_right hb 2609)
    simpa only [delta, h, OffsetTemplateDispatch.added] using hp.trans (Nat.add_le_add_left hbound A.bits.length)

theorem code_choice {n : ℕ} (c : ℤ) (vs : List (Fin n)) (suffix : List Bool) (hm : vs.length ≤ 4) :
    choice (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) = some vs.length := by
  rw [choice, List.append_assoc, SignedRawControl.rest_integer]
  exact OccurrenceDispatchControl.choice_code vs suffix 4 hm

theorem taken_code {n : ℕ} (c : ℤ) (vs : List (Fin n)) (suffix : List Bool) (hm : vs.length ≤ 4) :
    taken (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) =
      BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs :=
  SparseTermRawControl.taken_code c vs suffix 4 hm

theorem rest_code {n : ℕ} (c : ℤ) (vs : List (Fin n)) (suffix : List Bool) (hm : vs.length ≤ 4) :
    rest (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) = suffix :=
  SparseTermRawControl.rest_code c vs suffix 4 hm

theorem delta_code {n : ℕ} (boxed : Bool) (c : ℤ) (vs : List (Fin n)) (suffix : List Bool) (hm : vs.length ≤ 4) :
    delta boxed (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) =
      OffsetTemplateProgram.total (decide (c < 0)) c.natAbs (OffsetTemplateData.template boxed vs.length) := by
  rw [delta, code_choice c vs suffix hm, OffsetTemplateDispatch.added]
  simp only [List.append_assoc, SignedRawControl.negative_integer, SignedRawControl.magnitude_integer]

theorem count_code {n : ℕ} (c : ℤ) (vs : List (Fin n)) (suffix : List Bool) (hm : vs.length ≤ 4) :
    count (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) = 2 ^ vs.length := by
  rw [count, code_choice c vs suffix hm]

theorem cube_delta_code {n : ℕ} (c : ℤ) (vs : List (Fin n)) (suffix : List Bool) (hm : vs.length ≤ 4) :
    delta true (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) =
      OffsetTemplateData.rawSum (SparseSubstitution.cubeTerm 4 (c, vs)) := by
  rw [delta_code true c vs suffix hm]
  exact OffsetTemplateData.cube_total c vs

theorem orthant_delta_code {n : ℕ} (c : ℤ) (vs : List (Fin n)) (suffix : List Bool) (hm : vs.length ≤ 4) :
    delta false (BitCodec.integerCode c ++ SparseListCodec.listCode (SparseListCodec.finite n) vs ++ suffix) =
      OffsetTemplateData.rawSum (SparseInteger.scale c (SparseSubstitution.expand SparseSubstitution.orthantVariable vs)) := by
  rw [delta_code false c vs suffix hm]
  exact OffsetTemplateData.orthant_total c vs

end JointThermoComplexity.Complexity.SparseTermOffsetControl

#print axioms JointThermoComplexity.Complexity.SparseTermOffsetControl.result_bits
#print axioms JointThermoComplexity.Complexity.SparseTermOffsetControl.cube_delta_code
#print axioms JointThermoComplexity.Complexity.SparseTermOffsetControl.orthant_delta_code
