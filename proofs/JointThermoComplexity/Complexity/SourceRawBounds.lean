module
public import proofs.JointThermoComplexity.Complexity.SparseRawWeight
public import proofs.JointThermoComplexity.Complexity.SourceSparseFormula
public import proofs.JointThermoComplexity.Complexity.NumericSparseSource

set_option autoImplicit false
@[expose] public section

/-! # Raw term counts and coefficient bits of the executable source circuit

Each equation has at most three stored terms. Bounds apply before merging or
cancelling monomials, so they control the integers passed to serialization.
-/

namespace JointThermoComplexity.Complexity.SparseCircuit
open RealSyntax QuadraticCircuit SparseInteger
variable {n : ℕ} {V W : Type}
attribute [local simp] SparseInteger.length_product SparseInteger.length_square

def RawBound (B : ℕ) (p : Poly V) : Prop := p.length ≤ 3 ∧ rawWeight p ≤ B

theorem rawBound_mono {a b : ℕ} {p : Poly V} (hab : a ≤ b) (hp : RawBound a p) : RawBound b p :=
  ⟨hp.1, Nat.le_trans hp.2 hab⟩

theorem rawBound_relabel (f : V → W) {B : ℕ} {p : Poly V} (hp : RawBound B p) : RawBound B (relabel f p) := by
  simpa only [RawBound, length_relabel, rawWeight_relabel] using hp

theorem term_raw_bound (t : Term n) (p : Poly (Fin n ⊕ TermSlot t)) (hp : p ∈ termEquations t) :
    RawBound (3 + t.literalHeight) p := by
  induction t with
  | int z =>
    have he := List.mem_singleton.mp hp
    rw [he]
    simp only [RawBound, length_sub, length_atom, length_constant, rawWeight_sub,
      rawWeight_atom, rawWeight_constant, Term.literalHeight]
    constructor <;> omega
  | var v =>
    have he := List.mem_singleton.mp hp
    rw [he]
    simp [RawBound, Term.literalHeight]
  | add s t hs ht =>
    rcases List.mem_append.mp hp with hlr | hout
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
        exact rawBound_relabel _ (rawBound_mono (Nat.add_le_add_left (Nat.le_max_left _ _) 3) (hs q hq))
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact rawBound_relabel _ (rawBound_mono (Nat.add_le_add_left (Nat.le_max_right _ _) 3) (ht q hq))
    · have he := List.mem_singleton.mp hout
      rw [he]
      exact rawBound_mono (Nat.le_add_right 3 _) (by simp [RawBound])
  | mul s t hs ht =>
    rcases List.mem_append.mp hp with hlr | hout
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
        exact rawBound_relabel _ (rawBound_mono (Nat.add_le_add_left (Nat.le_max_left _ _) 3) (hs q hq))
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact rawBound_relabel _ (rawBound_mono (Nat.add_le_add_left (Nat.le_max_right _ _) 3) (ht q hq))
    · have he := List.mem_singleton.mp hout
      rw [he]
      exact rawBound_mono (Nat.le_add_right 3 _) (by simp [RawBound])
  | neg s hs =>
    rcases List.mem_append.mp hp with hl | hout
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
      exact rawBound_relabel _ (hs q hq)
    · have he := List.mem_singleton.mp hout
      rw [he]
      exact rawBound_mono (Nat.le_add_right 3 _) (by simp [RawBound])

theorem equality_raw_bound (p : Poly (Fin 3)) (hp : p ∈ equalityActivation) : RawBound 3 p := by
  simp only [equalityActivation, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp [RawBound]

theorem strictSign_raw_bound (p : Poly (Fin 6)) (hp : p ∈ strictSign) : RawBound 3 p := by
  simp only [strictSign, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp [RawBound]

theorem formula_raw_bound (p : Formula n) (q : Poly (Fin n ⊕ FormulaSlot p)) (hq : q ∈ formulaEquations p) :
    RawBound (3 + p.literalHeight) q := by
  induction p with
  | truth =>
    have he := List.mem_singleton.mp hq
    rw [he]
    simp [RawBound, Formula.literalHeight]
  | falsity =>
    have he := List.mem_singleton.mp hq
    rw [he]
    simp [RawBound, Formula.literalHeight]
  | eq s t =>
    rcases List.mem_append.mp hq with hlr | hg
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
        exact rawBound_relabel _ (rawBound_mono (Nat.add_le_add_left (Nat.le_max_left _ _) 3) (term_raw_bound s r hr))
      · obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hr
        exact rawBound_relabel _ (rawBound_mono (Nat.add_le_add_left (Nat.le_max_right _ _) 3) (term_raw_bound t r hmem))
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
      exact rawBound_relabel _ (rawBound_mono (Nat.le_add_right 3 _) (equality_raw_bound r hr))
  | lt s t =>
    rcases List.mem_append.mp hq with hlr | hg
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
        exact rawBound_relabel _ (rawBound_mono (Nat.add_le_add_left (Nat.le_max_left _ _) 3) (term_raw_bound s r hr))
      · obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hr
        exact rawBound_relabel _ (rawBound_mono (Nat.add_le_add_left (Nat.le_max_right _ _) 3) (term_raw_bound t r hmem))
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
      exact rawBound_relabel _ (rawBound_mono (Nat.le_add_right 3 _) (strictSign_raw_bound r hr))
  | conj p q hp hright =>
    rcases List.mem_append.mp hq with hlr | hout
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
        exact rawBound_relabel _ (rawBound_mono (Nat.add_le_add_left (Nat.le_max_left _ _) 3) (hp r hr))
      · obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hr
        exact rawBound_relabel _ (rawBound_mono (Nat.add_le_add_left (Nat.le_max_right _ _) 3) (hright r hmem))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
      rcases hout with rfl | rfl | rfl <;>
        exact rawBound_mono (Nat.le_add_right 3 _) (by simp [RawBound])
  | disj p q hp hright =>
    rcases List.mem_append.mp hq with hlr | hout
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hl
        exact rawBound_relabel _ (rawBound_mono (Nat.add_le_add_left (Nat.le_max_left _ _) 3) (hp r hr))
      · obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hr
        exact rawBound_relabel _ (rawBound_mono (Nat.add_le_add_left (Nat.le_max_right _ _) 3) (hright r hmem))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
      rcases hout with rfl | rfl <;>
        exact rawBound_mono (Nat.le_add_right 3 _) (by simp [RawBound])

theorem closed_raw_bound (p : Formula n) (q : Poly (Fin n ⊕ FormulaSlot p)) (hq : q ∈ closedEquations p) :
    RawBound (3 + p.literalHeight) q := by
  rcases List.mem_append.mp hq with hq | hq
  · exact formula_raw_bound p q hq
  · have he := List.mem_singleton.mp hq
    rw [he]
    exact rawBound_mono (Nat.le_add_right 3 _) (by simp [RawBound])

theorem numeric_raw_bound (s : Sentence) (p : Poly (Fin (SourceCoordinateEnumeration.sourceCount s)))
    (hp : p ∈ NumericSparseSource.equations s) : RawBound (3 + s.formula.literalHeight) p := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact rawBound_relabel _ (closed_raw_bound s.formula q hq)

theorem numeric_raw_term_count (s : Sentence) (p : Poly (Fin (SourceCoordinateEnumeration.sourceCount s)))
    (hp : p ∈ NumericSparseSource.equations s) : p.length ≤ 3 := (numeric_raw_bound s p hp).1

theorem numeric_raw_weight (s : Sentence) (p : Poly (Fin (SourceCoordinateEnumeration.sourceCount s)))
    (hp : p ∈ NumericSparseSource.equations s) : rawWeight p ≤ 3 + 2 ^ s.code.length :=
  Nat.le_trans (numeric_raw_bound s p hp).2 (Nat.add_le_add_left s.literalHeight_le_pow_code_length 3)

theorem numeric_raw_coefficient_bits (s : Sentence) (p : Poly (Fin (SourceCoordinateEnumeration.sourceCount s)))
    (hp : p ∈ NumericSparseSource.equations s) (a : ℤ × List (Fin (SourceCoordinateEnumeration.sourceCount s)))
    (ha : a ∈ p) : a.1.natAbs.bits.length ≤ s.code.length + 3 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have h := Nat.le_trans (rawWeight_member p a ha) (numeric_raw_weight s p hp)
  have hpos : 1 ≤ 2 ^ s.code.length := Nat.one_le_two_pow
  have hpow : 2 ^ (s.code.length + 3) = 8 * 2 ^ s.code.length := by rw [pow_add]; ring
  rw [hpow]
  omega

theorem numeric_raw_coefficient_code (s : Sentence) (p : Poly (Fin (SourceCoordinateEnumeration.sourceCount s)))
    (hp : p ∈ NumericSparseSource.equations s) (a : ℤ × List (Fin (SourceCoordinateEnumeration.sourceCount s)))
    (ha : a ∈ p) : (BitCodec.integerCode a.1).length ≤ 2 * s.code.length + 8 := by
  rw [BitCodec.integerCode_length]
  have h := numeric_raw_coefficient_bits s p hp a ha
  omega

end JointThermoComplexity.Complexity.SparseCircuit

#print axioms JointThermoComplexity.Complexity.SparseCircuit.closed_raw_bound
#print axioms JointThermoComplexity.Complexity.SparseCircuit.numeric_raw_term_count
#print axioms JointThermoComplexity.Complexity.SparseCircuit.numeric_raw_weight
#print axioms JointThermoComplexity.Complexity.SparseCircuit.numeric_raw_coefficient_code
