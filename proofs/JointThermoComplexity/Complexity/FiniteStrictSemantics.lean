module
public import proofs.JointThermoComplexity.Complexity.FinitePaddedGap
public import proofs.JointThermoComplexity.Complexity.SparseStrictSemantics

set_option autoImplicit false
@[expose] public section

/-! Exact strict-positivity equivalences for the generic finite-system data.
All schedules and integer coefficients are fixed before selecting a witness.
The binary construction runtime is a separate obligation.
-/

namespace JointThermoComplexity.Complexity.FiniteStrictSemantics
open EquationSystemCodec FiniteStrictData StrictPolynomialCore DInstabilityComplexity.Separation

noncomputable def system (p : Data) : Fin (paddedEquationCount p) → MvPolynomial (PaddedCoordinates p) ℤ :=
  fun j => SparseInteger.interpret (energyFamily p j)

theorem system_eq (p : Data) (j : Fin (paddedEquationCount p)) :
    system p j = FinitePaddedSemantics.paddedSystem p ((paddedIndexEnumeration p).symm j) :=
  FinitePaddedSemantics.interpret_padded p _

theorem energy_polynomial_eq (p : Data) : quadraticEnergyPolynomial (system p) =
    quadraticEnergyPolynomial (FinitePaddedSemantics.paddedSystem p) := by
  unfold quadraticEnergyPolynomial
  simp only [system_eq]
  exact (paddedIndexEnumeration p).symm.sum_comp (fun j => FinitePaddedSemantics.paddedSystem p j ^ 2)

theorem padded_witness (p : Data) (hp : FiniteEquationHardness.Domain p)
    (hf : FiniteEquationSemantics.Feasible p.rows) :
    ∃ u : PaddedCoordinates p → ℝ, InHalfCube u ∧ ∀ j, (system p j).eval₂ (Int.castRingHom ℝ) u = 0 := by
  obtain ⟨u, hu⟩ := (FinitePaddedSemantics.feasible_iff_padded_root p hp).mp hf
  refine ⟨u, FinitePaddedSemantics.padded_zero_half_interior p u hu, ?_⟩
  intro j
  rw [system_eq]
  exact hu ((paddedIndexEnumeration p).symm j)

theorem NO_gap (p : Data) (hp : FiniteEquationHardness.Domain p)
    (hn : ¬ FiniteEquationSemantics.Feasible p.rows) :
    ∀ u, (1 / 2 : ℝ) ^ (2 ^ thresholdCount p) < quadraticEnergy (system p) u := by
  intro u
  have h := FinitePaddedGap.NO_energy_above_threshold p hp hn u
  unfold quadraticEnergy
  rw [energy_polynomial_eq]
  exact h

theorem interpret_boundedUnnumbered (p : Data) :
    SparseInteger.interpret (boundedUnnumbered p) = StrictPolynomialCore.bounded (system p) (thresholdCount p) :=
  SparseStrictPolynomial.interpret_bounded (energyFamily p) (thresholdCount p)

theorem interpret_allRealUnnumbered (p : Data) :
    SparseInteger.interpret (allRealUnnumbered p) = StrictPolynomialCore.allReal (system p) (thresholdCount p) :=
  SparseStrictPolynomial.interpret_allReal (energyFamily p) (thresholdCount p)

theorem bounded_unnumbered_iff (p : Data) (hp : FiniteEquationHardness.Domain p) :
    FiniteEquationSemantics.Feasible p.rows ↔ ∃ v : Variables p → ℝ, InHalfCube v ∧
      0 < (SparseInteger.interpret (boundedUnnumbered p)).eval₂ (Int.castRingHom ℝ) v := by
  constructor
  · intro hf
    obtain ⟨u, hbox, hu⟩ := padded_witness p hp hf
    refine ⟨Sum.elim u (IntegerChainError.exactValues (thresholdCount p)), ?_, ?_⟩
    · intro i
      cases i with
      | inl i => exact hbox i
      | inr i => exact IntegerChainError.exactValues_half_interior _ i
    · rw [interpret_boundedUnnumbered]
      exact bounded_witness (system p) (thresholdCount p) u hu
  · rintro ⟨v, hbox, hpos⟩
    by_contra hn
    let u : PaddedCoordinates p → ℝ := fun i => v (.inl i)
    let y : Fin (thresholdCount p + 1) → ℝ := fun i => v (.inr i)
    have he : Sum.elim u y = v := by funext i; cases i <;> rfl
    have hstrict : 0 < (StrictPolynomialCore.bounded (system p) (thresholdCount p)).eval₂
        (Int.castRingHom ℝ) (Sum.elim u y) := by
      rw [he, ← interpret_boundedUnnumbered]
      exact hpos
    have ht : |y (Fin.last (thresholdCount p))| ≤ 1 := by
      have hb := abs_lt.mpr (hbox (.inr (Fin.last (thresholdCount p))))
      exact (hb.trans_le (by norm_num : (1 / 2 : ℝ) ≤ 1)).le
    exact bounded_excludes_gap (system p) (thresholdCount p) (NO_gap p hp hn) u y ht hstrict

theorem allReal_unnumbered_iff (p : Data) (hp : FiniteEquationHardness.Domain p) :
    FiniteEquationSemantics.Feasible p.rows ↔ ∃ v : Variables p → ℝ,
      0 < (SparseInteger.interpret (allRealUnnumbered p)).eval₂ (Int.castRingHom ℝ) v := by
  constructor
  · intro hf
    obtain ⟨u, _, hu⟩ := padded_witness p hp hf
    refine ⟨Sum.elim u (IntegerChainError.exactValues (thresholdCount p)), ?_⟩
    rw [interpret_allRealUnnumbered]
    exact allReal_witness (system p) (thresholdCount p) u hu
  · rintro ⟨v, hpos⟩
    by_contra hn
    let u : PaddedCoordinates p → ℝ := fun i => v (.inl i)
    let y : Fin (thresholdCount p + 1) → ℝ := fun i => v (.inr i)
    have he : Sum.elim u y = v := by funext i; cases i <;> rfl
    have hstrict : 0 < (StrictPolynomialCore.allReal (system p) (thresholdCount p)).eval₂
        (Int.castRingHom ℝ) (Sum.elim u y) := by
      rw [he, ← interpret_allRealUnnumbered]
      exact hpos
    exact allReal_excludes_gap (system p) (thresholdCount p) (NO_gap p hp hn) u y hstrict

theorem bounded_iff (p : Data) (hp : FiniteEquationHardness.Domain p) :
    FiniteEquationSemantics.Feasible p.rows ↔ ∃ v : Fin (variableCount p) → ℝ, InHalfCube v ∧
      0 < (SparseInteger.interpret (FiniteStrictData.bounded p)).eval₂ (Int.castRingHom ℝ) v := by
  constructor
  · intro hf
    obtain ⟨v, hbox, hpos⟩ := (bounded_unnumbered_iff p hp).mp hf
    refine ⟨v ∘ (variableEnumeration p).symm, ?_, ?_⟩
    · exact fun i => hbox ((variableEnumeration p).symm i)
    · rw [FiniteStrictData.bounded, SparseInteger.interpret_relabel, MvPolynomial.eval₂_rename]
      simpa only [Function.comp_def, Equiv.symm_apply_apply] using hpos
  · rintro ⟨v, hbox, hpos⟩
    apply (bounded_unnumbered_iff p hp).mpr
    refine ⟨v ∘ variableEnumeration p, (fun i => hbox (variableEnumeration p i)), ?_⟩
    simpa only [FiniteStrictData.bounded, SparseInteger.interpret_relabel, MvPolynomial.eval₂_rename] using hpos

theorem allReal_iff (p : Data) (hp : FiniteEquationHardness.Domain p) :
    FiniteEquationSemantics.Feasible p.rows ↔ ∃ v : Fin (variableCount p) → ℝ,
      0 < (SparseInteger.interpret (FiniteStrictData.allReal p)).eval₂ (Int.castRingHom ℝ) v := by
  constructor
  · intro hf
    obtain ⟨v, hpos⟩ := (allReal_unnumbered_iff p hp).mp hf
    refine ⟨v ∘ (variableEnumeration p).symm, ?_⟩
    rw [FiniteStrictData.allReal, SparseInteger.interpret_relabel, MvPolynomial.eval₂_rename]
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hpos
  · rintro ⟨v, hpos⟩
    apply (allReal_unnumbered_iff p hp).mpr
    refine ⟨v ∘ variableEnumeration p, ?_⟩
    simpa only [FiniteStrictData.allReal, SparseInteger.interpret_relabel, MvPolynomial.eval₂_rename] using hpos

end JointThermoComplexity.Complexity.FiniteStrictSemantics

#print axioms JointThermoComplexity.Complexity.FiniteStrictSemantics.padded_witness
#print axioms JointThermoComplexity.Complexity.FiniteStrictSemantics.NO_gap
#print axioms JointThermoComplexity.Complexity.FiniteStrictSemantics.bounded_iff
#print axioms JointThermoComplexity.Complexity.FiniteStrictSemantics.allReal_iff
