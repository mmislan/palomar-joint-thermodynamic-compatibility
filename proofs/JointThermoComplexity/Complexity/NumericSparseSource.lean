module
public import proofs.JointThermoComplexity.Complexity.SourceCoordinateEnumeration
public import proofs.JointThermoComplexity.Complexity.SourceSparseFormula
public import proofs.JointThermoComplexity.Complexity.SourceCircuitWeight

set_option autoImplicit false
@[expose] public section

/-! # Executable numeric sparse source equations

The actual data uses the explicit source enumeration and its explicit count.
The choice-based historical coordinate map appears only in a semantic
agreement theorem, through a proved finite reindexing.
-/

namespace JointThermoComplexity.Complexity.NumericSparseSource
open RealSyntax QuadraticCircuit SparseInteger SourceCoordinateEnumeration SourceIntegerWeight

def equations (s : Sentence) : List (Poly (Fin (sourceCount s))) :=
  (SparseCircuit.closedEquations s.formula).map (relabel (sourceEnumeration s))

noncomputable def semanticReindex (s : Sentence) : Fin (sourceArity s) ≃ Fin (sourceCount s) :=
  (sourceReindex s).symm.trans (sourceEnumeration s)

theorem equations_interpret (s : Sentence) :
    (equations s).map interpret = (closedFormulaEquations s.formula).map (MvPolynomial.rename (sourceEnumeration s)) := by
  rw [equations, SparseCircuit.interpret_relabel_list, SparseCircuit.closed_interpret]

theorem equations_agree (s : Sentence) :
    (equations s).map interpret = (sourceEquations s).map (MvPolynomial.rename (semanticReindex s)) := by
  rw [equations_interpret, sourceEquations, List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_def, MvPolynomial.rename_rename]
  have hfun : (sourceEnumeration s : SourceVariables s → Fin (sourceCount s)) =
      (semanticReindex s) ∘ sourceReindex s := by
    funext i
    simp [semanticReindex, Function.comp_def]
  rw [hfun]
  rfl

theorem satisfiable_iff (s : Sentence) :
    s.Satisfiable ↔ ∃ x : Fin (sourceCount s) → ℝ,
      ∀ p ∈ equations s, (interpret p).eval₂ (Int.castRingHom ℝ) x = 0 := by
  constructor
  · intro hs
    obtain ⟨u, hu⟩ := (SparseCircuit.closed_satisfiable_iff s.formula).mpr hs
    refine ⟨u ∘ (sourceEnumeration s).symm, ?_⟩
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [interpret_relabel, MvPolynomial.eval₂_rename]
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hu q hq
  · rintro ⟨x, hx⟩
    apply (SparseCircuit.closed_satisfiable_iff s.formula).mp
    refine ⟨x ∘ sourceEnumeration s, ?_⟩
    intro q hq
    have h := hx (relabel (sourceEnumeration s) q) (List.mem_map.mpr ⟨q, hq, rfl⟩)
    simpa only [interpret_relabel, MvPolynomial.eval₂_rename] using h

theorem equation_count (s : Sentence) : (equations s).length ≤ 4 * s.code.length + 1 := by
  have h := sourceEquations_length_le_code_length s
  rw [← List.length_map (f := interpret), equations_agree, List.length_map]
  exact h

theorem coordinate_count (s : Sentence) : sourceCount s ≤ 5 * s.code.length := sourceCount_le_code_length s

theorem equation_degree (s : Sentence) (p : Poly (Fin (sourceCount s))) (hp : p ∈ equations s) :
    (interpret p).totalDegree ≤ 2 := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  rw [interpret_relabel]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans (SparseCircuit.closed_equations_degree s.formula q hq)

theorem equation_weight (s : Sentence) (p : Poly (Fin (sourceCount s))) (hp : p ∈ equations s) :
    weight (interpret p) ≤ 3 + s.formula.literalHeight := by
  have hm : interpret p ∈ (equations s).map interpret := List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [equations_agree] at hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  rw [← he]
  exact (weight_rename _ _).trans (sourceEquations_weight s q hq)

theorem coefficient_natAbs (s : Sentence) (p : Poly (Fin (sourceCount s))) (hp : p ∈ equations s)
    (d : Fin (sourceCount s) →₀ ℕ) : ((interpret p).coeff d).natAbs ≤ 3 + 2 ^ s.code.length :=
  (weight_coeff _ _).trans ((equation_weight s p hp).trans
    (Nat.add_le_add_left s.literalHeight_le_pow_code_length 3))

theorem coefficient_bits (s : Sentence) (p : Poly (Fin (sourceCount s))) (hp : p ∈ equations s)
    (d : Fin (sourceCount s) →₀ ℕ) : ((interpret p).coeff d).natAbs.bits.length ≤ s.code.length + 3 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have h := coefficient_natAbs s p hp d
  have hpos : 1 ≤ 2 ^ s.code.length := Nat.one_le_two_pow
  have hpow : 2 ^ (s.code.length + 3) = 8 * 2 ^ s.code.length := by rw [pow_add]; ring
  rw [hpow]
  omega

theorem coefficient_code (s : Sentence) (p : Poly (Fin (sourceCount s))) (hp : p ∈ equations s)
    (d : Fin (sourceCount s) →₀ ℕ) : (BitCodec.integerCode ((interpret p).coeff d)).length ≤ 2 * s.code.length + 8 := by
  rw [BitCodec.integerCode_length]
  have h := coefficient_bits s p hp d
  omega

end JointThermoComplexity.Complexity.NumericSparseSource

#print axioms JointThermoComplexity.Complexity.NumericSparseSource.equations
#print axioms JointThermoComplexity.Complexity.NumericSparseSource.equations_agree
#print axioms JointThermoComplexity.Complexity.NumericSparseSource.satisfiable_iff
#print axioms JointThermoComplexity.Complexity.NumericSparseSource.equation_degree
#print axioms JointThermoComplexity.Complexity.NumericSparseSource.coefficient_code
