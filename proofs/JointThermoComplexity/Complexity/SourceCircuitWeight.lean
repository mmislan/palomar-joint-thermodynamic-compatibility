module
public import proofs.JointThermoComplexity.Complexity.SourceClosedQuadratic
public import proofs.JointThermoComplexity.Complexity.SourceLiteralHeight
public import proofs.JointThermoComplexity.Complexity.SourceIntegerWeight

set_option autoImplicit false
@[expose] public section

/-! # Linear bit-length bounds for every coefficient of the source normal form

No term product is expanded in this construction. Every operation or
activation equation has coefficient weight at most three, except for the
literal equations whose weight also includes the original integer literal.
These bounds apply after the finite coordinate reindexing as well.
-/

namespace JointThermoComplexity.Complexity.QuadraticCircuit
open RealSyntax MvPolynomial SourceIntegerWeight
variable {n : ℕ}

theorem termEquations_weight (t : Term n) (p : MvPolynomial (Fin n ⊕ TermSlot t) ℤ)
    (hp : p ∈ termEquations t) : weight p ≤ 3 + t.literalHeight := by
  induction t with
  | int z =>
    have he := List.mem_singleton.mp hp
    rw [he]
    apply (weight_sub _ _).trans
    simp only [weight_X, weight_C, Term.literalHeight]
    omega
  | var v =>
    have he := List.mem_singleton.mp hp
    rw [he]
    exact (weight_X_sub_X _ _).trans (by decide : 2 ≤ 3)
  | add s t hs ht =>
    rcases List.mem_append.mp hp with hlr | hout
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
        exact (weight_rename _ _).trans ((hs q hq).trans
          (Nat.add_le_add_left (Nat.le_max_left _ _) 3))
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact (weight_rename _ _).trans ((ht q hq).trans
          (Nat.add_le_add_left (Nat.le_max_right _ _) 3))
    · have he := List.mem_singleton.mp hout
      rw [he]
      exact (weight_X_sub_add _ _ _).trans (Nat.le_add_right _ _)
  | mul s t hs ht =>
    rcases List.mem_append.mp hp with hlr | hout
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
        exact (weight_rename _ _).trans ((hs q hq).trans
          (Nat.add_le_add_left (Nat.le_max_left _ _) 3))
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact (weight_rename _ _).trans ((ht q hq).trans
          (Nat.add_le_add_left (Nat.le_max_right _ _) 3))
    · have he := List.mem_singleton.mp hout
      rw [he]
      exact (weight_X_sub_mul _ _ _).trans (by omega)
  | neg s hs =>
    rcases List.mem_append.mp hp with hl | hout
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
      exact (weight_rename _ _).trans (hs q hq)
    · have he := List.mem_singleton.mp hout
      rw [he]
      exact (weight_X_add_X _ _).trans (by omega)

theorem equalityActivationEquations_weight (p : MvPolynomial (Fin 3) ℤ)
    (hp : p ∈ equalityActivationEquations) : weight p ≤ 3 := by
  simp only [equalityActivationEquations, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact (weight_boolean _).trans (by decide : 2 ≤ 3)
  · exact (weight_X_mul_difference _ _ _).trans (by decide : 2 ≤ 3)

theorem strictSignEquations_weight (p : MvPolynomial (Fin 6) ℤ)
    (hp : p ∈ strictSignEquations) : weight p ≤ 3 := by
  simp only [strictSignEquations, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact (weight_boolean _).trans (by decide : 2 ≤ 3)
  · exact (weight_X_sub_sq _ _).trans (by decide : 2 ≤ 3)
  · exact weight_X_sub_difference_mul _ _ _ _
  · have h := weight_mul (X 0 : MvPolynomial (Fin 6) ℤ) (X 5 - 1)
    have hd := weight_X_sub_one (V := Fin 6) 5
    simp only [weight_X, one_mul] at h
    omega

theorem formulaEquations_weight (p : Formula n)
    (f : MvPolynomial (Fin n ⊕ FormulaSlot p) ℤ) (hf : f ∈ formulaEquations p) :
    weight f ≤ 3 + p.literalHeight := by
  induction p with
  | truth =>
    have he := List.mem_singleton.mp hf
    rw [he]
    exact (weight_boolean _).trans (by decide : 2 ≤ 3)
  | falsity =>
    have he := List.mem_singleton.mp hf
    rw [he, weight_X]
    change 1 ≤ 3
    decide
  | eq s t =>
    rcases List.mem_append.mp hf with hlr | hg
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
        exact (weight_rename _ _).trans ((termEquations_weight s q hq).trans
          (Nat.add_le_add_left (Nat.le_max_left _ _) 3))
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact (weight_rename _ _).trans ((termEquations_weight t q hq).trans
          (Nat.add_le_add_left (Nat.le_max_right _ _) 3))
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
      exact (weight_rename _ _).trans ((equalityActivationEquations_weight q hq).trans (Nat.le_add_right _ _))
  | lt s t =>
    rcases List.mem_append.mp hf with hlr | hg
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
        exact (weight_rename _ _).trans ((termEquations_weight s q hq).trans
          (Nat.add_le_add_left (Nat.le_max_left _ _) 3))
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact (weight_rename _ _).trans ((termEquations_weight t q hq).trans
          (Nat.add_le_add_left (Nat.le_max_right _ _) 3))
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
      exact (weight_rename _ _).trans ((strictSignEquations_weight q hq).trans (Nat.le_add_right _ _))
  | conj p q hp hq =>
    rcases List.mem_append.mp hf with hlr | hout
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hl
        exact (weight_rename _ _).trans ((hp g hg).trans
          (Nat.add_le_add_left (Nat.le_max_left _ _) 3))
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
        exact (weight_rename _ _).trans ((hq g hg).trans
          (Nat.add_le_add_left (Nat.le_max_right _ _) 3))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
      rcases hout with rfl | rfl | rfl
      · exact (weight_boolean _).trans (by omega)
      · exact (weight_X_sub_X _ _).trans (by omega)
      · exact (weight_X_sub_X _ _).trans (by omega)
  | disj p q hp hq =>
    rcases List.mem_append.mp hf with hlr | hout
    · rcases List.mem_append.mp hlr with hl | hr
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hl
        exact (weight_rename _ _).trans ((hp g hg).trans
          (Nat.add_le_add_left (Nat.le_max_left _ _) 3))
      · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
        exact (weight_rename _ _).trans ((hq g hg).trans
          (Nat.add_le_add_left (Nat.le_max_right _ _) 3))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
      rcases hout with rfl | rfl
      · exact (weight_boolean _).trans (by omega)
      · exact (weight_add_sub_X _ _ _).trans (Nat.le_add_right _ _)

theorem sourceEquations_weight (s : Sentence)
    (f : MvPolynomial (Fin (sourceArity s)) ℤ) (hf : f ∈ sourceEquations s) :
    weight f ≤ 3 + s.formula.literalHeight := by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  apply (weight_rename _ _).trans
  rcases List.mem_append.mp hg with hg | hg
  · exact formulaEquations_weight s.formula g hg
  · have he := List.mem_singleton.mp hg
    rw [he]
    exact (weight_X_sub_one _).trans (by omega)

theorem sourceEquations_coeff_natAbs_le (s : Sentence)
    (f : MvPolynomial (Fin (sourceArity s)) ℤ) (hf : f ∈ sourceEquations s)
    (d : Fin (sourceArity s) →₀ ℕ) : (f.coeff d).natAbs ≤ 3 + 2 ^ s.code.length :=
  (weight_coeff f d).trans ((sourceEquations_weight s f hf).trans
    (Nat.add_le_add_left s.literalHeight_le_pow_code_length 3))

theorem sourceEquations_coeff_bits_length_le (s : Sentence)
    (f : MvPolynomial (Fin (sourceArity s)) ℤ) (hf : f ∈ sourceEquations s)
    (d : Fin (sourceArity s) →₀ ℕ) : (f.coeff d).natAbs.bits.length ≤ s.code.length + 3 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have h := sourceEquations_coeff_natAbs_le s f hf d
  have hpos : 1 ≤ 2 ^ s.code.length := Nat.one_le_pow _ _ (by decide)
  have hpow : 2 ^ (s.code.length + 3) = 8 * 2 ^ s.code.length := by
    rw [pow_add]; ring
  rw [hpow]
  omega

theorem sourceEquations_coeff_code_length_le (s : Sentence)
    (f : MvPolynomial (Fin (sourceArity s)) ℤ) (hf : f ∈ sourceEquations s)
    (d : Fin (sourceArity s) →₀ ℕ) :
    (BitCodec.integerCode (f.coeff d)).length ≤ 2 * s.code.length + 8 := by
  rw [BitCodec.integerCode_length]
  have h := sourceEquations_coeff_bits_length_le s f hf d
  omega

end JointThermoComplexity.Complexity.QuadraticCircuit

#print axioms JointThermoComplexity.Complexity.QuadraticCircuit.sourceEquations_weight
#print axioms JointThermoComplexity.Complexity.QuadraticCircuit.sourceEquations_coeff_natAbs_le
#print axioms JointThermoComplexity.Complexity.QuadraticCircuit.sourceEquations_coeff_code_length_le
