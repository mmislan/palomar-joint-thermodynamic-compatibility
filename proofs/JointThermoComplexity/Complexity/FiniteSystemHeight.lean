module
public import proofs.JointThermoComplexity.Complexity.FiniteStrictBounds
public import proofs.JointThermoComplexity.Complexity.NumericSourceHeight

set_option autoImplicit false
@[expose] public section

/-! Effective common-witness bounds for parsed small quadratic systems.
The scale length is computed only from the faithful input-code length.
-/

namespace JointThermoComplexity.Complexity.FiniteSystemHeight
open SparseInteger EquationSystemCodec FiniteStrictData SourceIntegerWeight NaturalHeightBounds
open QuarterScaleSchedule FixedQuarterSquaring SourceHeightSchedules DInstabilityComplexity.Separation

theorem monomial_weight_le {V : Type} (vs : List V) : weight (monomial vs) ≤ 1 := by
  induction vs with
  | nil => simp only [monomial_nil, weight_one, le_refl]
  | cons v vs ih =>
    rw [monomial_cons]
    exact (weight_mul _ _).trans (by simpa only [weight_X, Nat.one_mul] using ih)

theorem interpret_weight_le {V : Type} (p : SparseInteger.Poly V) : weight (interpret p) ≤ rawWeight p := by
  induction p with
  | nil => simp only [interpret_nil, weight, integerWeight.mvWeight_zero, rawWeight_nil, le_refl]
  | cons a p ih =>
    rw [interpret_cons, rawWeight_cons]
    apply (weight_add _ _).trans
    apply Nat.add_le_add _ ih
    have h := (weight_mul (MvPolynomial.C a.1) (monomial a.2)).trans
      (Nat.mul_le_mul (weight_C a.1).le (monomial_weight_le a.2))
    simpa only [Nat.mul_one] using h

noncomputable def system (p : Data) : OriginalIndices p → MvPolynomial (Fin p.arity) ℤ :=
  fun j => interpret (original p j)

noncomputable def height (p : Data) : ℕ := quadraticCoordinateHeight p.arity (quadraticCriticalLength (system p))

theorem system_degree (p : Data) (hp : FiniteEquationHardness.Domain p) (j : OriginalIndices p) :
    (system p j).totalDegree ≤ 2 := (hp.2 _ (List.getElem_mem j.isLt)).2

theorem feasible_iff_root (p : Data) : FiniteEquationSemantics.Feasible p.rows ↔
    ∃ x, ∀ j, (system p j).eval₂ (Int.castRingHom ℝ) x = 0 := by
  apply exists_congr
  intro x
  exact (original_holds_iff p x).symm

theorem system_weight (p : Data) (hp : FiniteEquationHardness.Domain p) (j : OriginalIndices p) :
    weight (system p j) ≤ 3 + 2 ^ inputLength p := by
  have h := (interpret_weight_le (original p j)).trans (FiniteStrictBounds.original_weight p hp j)
  change weight (system p j) ≤ 5 at h
  have he : 2 ≤ 2 ^ inputLength p := by
    have hpos : 0 < inputLength p := EquationCodeBounds.length_pos p
    have hle : 1 ≤ inputLength p := by omega
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hle
  omega

theorem squared_length (p : Data) (hp : FiniteEquationHardness.Domain p) :
    quadraticSquaredLength (system p) ≤ (4 * inputLength p + 1) * (3 + 2 ^ inputLength p) ^ 2 := by
  classical
  unfold quadraticSquaredLength
  calc
    _ ≤ ∑ _j : OriginalIndices p, (3 + 2 ^ inputLength p) ^ 2 :=
      Finset.sum_le_sum (fun j _ => Nat.pow_le_pow_left (system_weight p hp j) 2)
    _ = p.rows.length * (3 + 2 ^ inputLength p) ^ 2 := by simp [OriginalIndices]
    _ ≤ _ := Nat.mul_le_mul_right _ (by have hn : p.rows.length ≤ inputLength p := EquationCodeBounds.rows_le_length p; omega)

theorem critical_power (p : Data) (hp : FiniteEquationHardness.Domain p) :
    quadraticCriticalLength (system p) ≤ 2 ^ (3 * inputLength p + 11) := by
  let L := inputLength p
  have hM : 4 * L + 1 ≤ 2 ^ (L + 3) := by
    calc
      _ ≤ 4 * (L + 1) := by omega
      _ ≤ 4 * 2 ^ (L + 1) := Nat.mul_le_mul_left 4 (Nat.lt_two_pow_self : L + 1 < 2 ^ (L + 1)).le
      _ = _ := by rw [show L + 3 = (L + 1) + 2 by omega, pow_add]; ring
  have hW : 3 + 2 ^ L ≤ 2 ^ (L + 2) := by
    have hpos : 1 ≤ 2 ^ L := Nat.one_le_two_pow
    have he : 2 ^ (L + 2) = 4 * 2 ^ L := by rw [pow_add]; ring
    rw [he]
    omega
  have h := critical_length_power_bound (quadraticSquaredLength (system p))
    (4 * L + 1) (3 + 2 ^ L) (L + 3) (L + 2) (squared_length p hp) hM hW
  have he : (L + 3) + 2 * (L + 2) + 4 = 3 * L + 11 := by omega
  rw [he] at h
  exact h

theorem height_le_cap (p : Data) : height p ≤ heightCap p.arity (quadraticCriticalLength (system p)) := by
  have hC : 1 ≤ quadraticCriticalLength (system p) := by unfold quadraticCriticalLength; omega
  exact witness_form_le_cap p.arity _ hC

theorem exists_bounded (p : Data) (hp : FiniteEquationHardness.Domain p)
    (hf : FiniteEquationSemantics.Feasible p.rows) :
    ∃ x, (∀ j, (system p j).eval₂ (Int.castRingHom ℝ) x = 0) ∧ ∀ i, |x i| < (height p : ℝ) + 1 := by
  obtain ⟨x, hx, hb⟩ := exists_effectively_bounded_quadratic_solution (system p) (system_degree p hp)
    ((feasible_iff_root p).mp hf)
  exact ⟨x, hx, by simpa only [height, Fintype.card_fin] using hb⟩

theorem scale_schedule_eq (p : Data) : scaleCount p = sourceChainLength (inputLength p) :=
  (sourceChainLength_formula (inputLength p)).symm

theorem chosen_scale_bound (p : Data) (hp : FiniteEquationHardness.Domain p) :
    exactChain (scaleCount p) * ((height p : ℝ) + 1) ≤ 1 / 4 := by
  rw [scale_schedule_eq]
  have hn : p.arity ≤ 5 * inputLength p := by have hn : p.arity ≤ inputLength p := EquationCodeBounds.arity_le_length p; omega
  exact quarter_scale_from_cap p.arity (quadraticCriticalLength (system p)) (3 * inputLength p + 11)
    (height p) (sourceChainLength (inputLength p)) (critical_power p hp) (height_le_cap p)
    (Nat.add_le_add_right (exponent_monotone hn le_rfl) 1)

end JointThermoComplexity.Complexity.FiniteSystemHeight

#print axioms JointThermoComplexity.Complexity.FiniteSystemHeight.interpret_weight_le
#print axioms JointThermoComplexity.Complexity.FiniteSystemHeight.feasible_iff_root
#print axioms JointThermoComplexity.Complexity.FiniteSystemHeight.exists_bounded
#print axioms JointThermoComplexity.Complexity.FiniteSystemHeight.chosen_scale_bound
