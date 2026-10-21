module
public import proofs.JointThermoComplexity.Complexity.SparseDimensionEmit

set_option autoImplicit false
@[expose] public section

/-! Actual complete source first pass followed by concrete network headers. -/

namespace JointThermoComplexity.Complexity.SparseDimensionEntry
open _root_.Complexity _root_.Complexity.TM
open SparseOffsetPorts

def outcome (boxed : Bool) (input : List Bool) : CountedSparseControl.State :=
  CountedSparseControl.run boxed input.length (SparseCountedEntry.state input)

def machine (boxed : Bool) : TM 33 := seqTM (SparseCountedEntry.machine boxed) (SparseDimensionEmit.machine boxed)
def timeBound (L : ℕ) : ℕ := SparseCountedEntry.timeBound L + 1 + SparseDimensionEmit.bound L

theorem rows_bound (boxed : Bool) (input : List Bool) : (outcome boxed input).rows ≤ 16 * input.length := by
  simpa only [outcome, SparseCountedEntry.state, Nat.zero_add] using
    CountedSparseControl.run_rows_bound boxed input.length (SparseCountedEntry.state input)

theorem hoareTime (boxed : Bool) (input : List Bool) :
    (machine boxed).HoareTime (SparseInputInitialization.Initial input)
      (SparseDimensionEmit.Pred input.length (HeaderControl.count input) (outcome boxed input)
        (SparseDimensionWords.header boxed (HeaderControl.count input) (outcome boxed input).rows))
      (timeBound input.length) := by
  have hp := SparseCountedEntry.hoareTime boxed input
  have hh := SparseDimensionEmit.hoareTime boxed input.length (HeaderControl.count input) (outcome boxed input)
    (HeaderControl.count_le_length input) (rows_bound boxed input) []
  have hs := seqTM_hoareTime _ _ hp (SparseDimensionEmit.phase input.length (HeaderControl.count input) (outcome boxed input) []) hh
  apply hs.consequence
  · exact fun _ _ _ hp => hp
  · intro inp work out hp
    simpa only [List.nil_append] using hp
  · exact le_rfl

theorem cubic_timeBound (L : ℕ) :
    timeBound L = 3328 * L ^ 3 + 8692651 * L ^ 2 + 10898578 * L + 80 := by
  unfold timeBound SparseDimensionEmit.bound
  rw [SparseCountedEntry.cubic_timeBound]
  ring1

theorem outcome_code (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (hp : SparseInteger.DegreeLE 4 p.payload) : outcome boxed (SparsePolynomialCodec.code p) =
      ⟨⟨false, SparsePolynomialCodec.code p, [], 1 + SparseOffsetCode.total boxed p.payload⟩,
        CountedSparseCode.rowTotal p.payload⟩ := by
  have hk : p.payload.length + 1 ≤ (SparsePolynomialCodec.code p).length := by
    have hf := SparseOffsetCode.enough_fuel p.payload
    rw [SparseCountedEntry.code_eq, List.length_append]
    omega
  have hr := CountedSparseCode.run_code boxed p.payload hp (SparsePolynomialCodec.code p).length hk
    (RealSyntax.binderCode p.arity) [] 1 0
  simp only [List.append_nil, Nat.zero_add] at hr
  unfold outcome
  rw [SparseCountedEntry.state_code, hr, ← SparseCountedEntry.code_eq]

theorem canonical_hoareTime (boxed : Bool) (p : SparsePolynomialCodec.PolynomialData)
    (hp : SparseInteger.DegreeLE 4 p.payload) :
    (machine boxed).HoareTime (SparseInputInitialization.Initial (SparsePolynomialCodec.code p))
      (SparseDimensionEmit.Pred (SparsePolynomialCodec.code p).length p.arity
        ⟨⟨false, SparsePolynomialCodec.code p, [], 1 + SparseOffsetCode.total boxed p.payload⟩,
          CountedSparseCode.rowTotal p.payload⟩
        (SparseDimensionWords.header boxed p.arity (CountedSparseCode.rowTotal p.payload)))
      (timeBound (SparsePolynomialCodec.code p).length) := by
  have ht := hoareTime boxed (SparsePolynomialCodec.code p)
  rw [SparseCountedEntry.count_code, outcome_code boxed p hp] at ht
  exact ht

end JointThermoComplexity.Complexity.SparseDimensionEntry

#print axioms JointThermoComplexity.Complexity.SparseDimensionEntry.hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDimensionEntry.canonical_hoareTime
#print axioms JointThermoComplexity.Complexity.SparseDimensionEntry.cubic_timeBound
