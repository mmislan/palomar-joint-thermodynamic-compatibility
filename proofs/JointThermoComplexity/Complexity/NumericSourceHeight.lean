module
public import proofs.JointThermoComplexity.Complexity.SparseScaledSource
public import proofs.JointThermoComplexity.Complexity.SourceHeightSchedules

set_option autoImplicit false
@[expose] public section

/-! # Effective common-witness height for the explicitly numbered source

The common witness is derived from the generic checked integer-quadratic
bound. The same polynomial chain-length schedule is adequate for the explicit
numbering; no witness or height certificate is part of the source input.
-/

namespace JointThermoComplexity.Complexity.NumericSourceHeight
open RealSyntax SourceCoordinateEnumeration SourceIntegerWeight NaturalHeightBounds
open QuarterScaleSchedule FixedQuarterSquaring SourceHeightSchedules DInstabilityComplexity.Separation

noncomputable def system (s : Sentence) : SparseScaledSource.OriginalIndices s → MvPolynomial (Fin (sourceCount s)) ℤ :=
  fun j => SparseInteger.interpret (SparseScaledSource.original s j)

noncomputable def height (s : Sentence) : ℕ :=
  quadraticCoordinateHeight (sourceCount s) (quadraticCriticalLength (system s))

theorem system_degree (s : Sentence) (j : SparseScaledSource.OriginalIndices s) : (system s j).totalDegree ≤ 2 :=
  SparseScaledSource.original_degree s j

theorem source_iff_system_root (s : Sentence) :
    s.Satisfiable ↔ ∃ x, ∀ j, (system s j).eval₂ (Int.castRingHom ℝ) x = 0 := by
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := (NumericSparseSource.satisfiable_iff s).mp hs
    exact ⟨x, (SparseScaledSource.original_holds_iff s x).mpr hx⟩
  · rintro ⟨x, hx⟩
    exact (NumericSparseSource.satisfiable_iff s).mpr ⟨x, (SparseScaledSource.original_holds_iff s x).mp hx⟩

theorem system_weight (s : Sentence) (j : SparseScaledSource.OriginalIndices s) :
    weight (system s j) ≤ 3 + 2 ^ s.code.length :=
  (NumericSparseSource.equation_weight s _ (List.getElem_mem j.isLt)).trans
    (Nat.add_le_add_left s.literalHeight_le_pow_code_length 3)

theorem squared_length (s : Sentence) :
    quadraticSquaredLength (system s) ≤ (4 * s.code.length + 1) * (3 + 2 ^ s.code.length) ^ 2 := by
  classical
  unfold quadraticSquaredLength
  calc
    _ ≤ ∑ _j : SparseScaledSource.OriginalIndices s, (3 + 2 ^ s.code.length) ^ 2 :=
      Finset.sum_le_sum (fun j _ => Nat.pow_le_pow_left (system_weight s j) 2)
    _ = (NumericSparseSource.equations s).length * (3 + 2 ^ s.code.length) ^ 2 := by simp [SparseScaledSource.OriginalIndices]
    _ ≤ _ := Nat.mul_le_mul_right _ (NumericSparseSource.equation_count s)

theorem critical_power (s : Sentence) :
    quadraticCriticalLength (system s) ≤ 2 ^ (3 * s.code.length + 11) := by
  let L := s.code.length
  have hM : 4 * L + 1 ≤ 2 ^ (L + 3) := by
    calc
      _ ≤ 4 * (L + 1) := by omega
      _ ≤ 4 * 2 ^ (L + 1) := Nat.mul_le_mul_left 4 (Nat.lt_two_pow_self : L + 1 < 2 ^ (L + 1)).le
      _ = _ := by rw [show L + 3 = (L + 1) + 2 by omega, pow_add]; ring
  have hW : 3 + 2 ^ L ≤ 2 ^ (L + 2) := by
    have hp : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have he : 2 ^ (L + 2) = 4 * 2 ^ L := by rw [pow_add]; ring
    rw [he]
    omega
  have h := critical_length_power_bound (quadraticSquaredLength (system s))
    (4 * L + 1) (3 + 2 ^ L) (L + 3) (L + 2) (squared_length s) hM hW
  have he : (L + 3) + 2 * (L + 2) + 4 = 3 * L + 11 := by omega
  rw [he] at h
  exact h

theorem height_le_cap (s : Sentence) :
    height s ≤ heightCap (sourceCount s) (quadraticCriticalLength (system s)) := by
  have hC : 1 ≤ quadraticCriticalLength (system s) := by unfold quadraticCriticalLength; omega
  exact witness_form_le_cap (sourceCount s) (quadraticCriticalLength (system s)) hC

theorem exists_bounded (s : Sentence) (hs : s.Satisfiable) :
    ∃ x : Fin (sourceCount s) → ℝ, (∀ j, (system s j).eval₂ (Int.castRingHom ℝ) x = 0) ∧
      ∀ i, |x i| < (height s : ℝ) + 1 := by
  obtain ⟨x, hx, hb⟩ := exists_effectively_bounded_quadratic_solution (system s) (system_degree s)
    ((source_iff_system_root s).mp hs)
  exact ⟨x, hx, by simpa only [height, Fintype.card_fin] using hb⟩

theorem chosen_scale_bound (s : Sentence) :
    exactChain (sourceChainLength s.code.length) * ((height s : ℝ) + 1) ≤ 1 / 4 :=
  quarter_scale_from_cap (sourceCount s) (quadraticCriticalLength (system s)) (3 * s.code.length + 11)
    (height s) (sourceChainLength s.code.length) (critical_power s) (height_le_cap s)
    (Nat.add_le_add_right (exponent_monotone (sourceCount_le_code_length s) le_rfl) 1)

end JointThermoComplexity.Complexity.NumericSourceHeight

#print axioms JointThermoComplexity.Complexity.NumericSourceHeight.source_iff_system_root
#print axioms JointThermoComplexity.Complexity.NumericSourceHeight.critical_power
#print axioms JointThermoComplexity.Complexity.NumericSourceHeight.exists_bounded
#print axioms JointThermoComplexity.Complexity.NumericSourceHeight.chosen_scale_bound
