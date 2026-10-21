module
public import proofs.JointThermoComplexity.Complexity.NumberedFormulaEquations
public import proofs.JointThermoComplexity.Complexity.SourceRawBounds
public import proofs.JointThermoComplexity.Complexity.SourceSmallLiteralSentence

set_option autoImplicit false
@[expose] public section

/-! The explicit natural-ID equation stream agrees byte-for-data with the accepted finite numbering. -/

namespace JointThermoComplexity.Complexity.NumberedSourceEquations
open RealSyntax SparseInteger SourceCoordinateEnumeration NumberedTermEquations

def equations (s : Sentence) : List (Poly ℕ) := NumberedFormulaEquations.closed s.formula Fin.val s.arity

theorem address_eq (s : Sentence) :
    NumberedFormulaEquations.address s.formula Fin.val s.arity = Fin.val ∘ sourceEnumeration s := by
  funext v
  cases v with
  | inl i => rfl
  | inr a =>
    change s.arity + NumberedFormulaEquations.slot s.formula a = s.arity + (formulaEnumeration s.formula a).val
    rw [NumberedFormulaEquations.slot_eq_enumeration]

theorem equations_agree (s : Sentence) :
    (NumericSparseSource.equations s).map (relabel Fin.val) = equations s := by
  rw [NumericSparseSource.equations, map_relabel_comp, ← address_eq]
  exact NumberedFormulaEquations.closed_agree s.formula Fin.val s.arity

theorem equation_count (s : Sentence) : (equations s).length = (NumericSparseSource.equations s).length := by
  rw [← equations_agree, List.length_map]

theorem equation_count_bound (s : Sentence) : (equations s).length ≤ 4 * s.code.length + 1 := by
  rw [equation_count]
  exact NumericSparseSource.equation_count s

theorem coordinate_bound (s : Sentence) (q : Poly ℕ) (hq : q ∈ equations s) (a : ℤ × List ℕ) (ha : a ∈ q)
    (v : ℕ) (hv : v ∈ a.2) : v < sourceCount s := by
  rw [← equations_agree] at hq
  obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp hq
  obtain ⟨b, _hb, rfl⟩ := List.mem_map.mp ha
  obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hv
  exact i.isLt

theorem raw_bound (s : Sentence) (q : Poly ℕ) (hq : q ∈ equations s) :
    SparseCircuit.RawBound (3 + s.formula.literalHeight) q := by
  rw [← equations_agree] at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  exact SparseCircuit.rawBound_relabel _ (SparseCircuit.numeric_raw_bound s p hp)

theorem satisfiable_iff (s : Sentence) : s.Satisfiable ↔
    ∃ x : ℕ → ℝ, ∀ q ∈ equations s, (interpret q).eval₂ (Int.castRingHom ℝ) x = 0 := by
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := (NumericSparseSource.satisfiable_iff s).mp hs
    let u : ℕ → ℝ := fun i => if hi : i < sourceCount s then x ⟨i, hi⟩ else 0
    refine ⟨u, ?_⟩
    intro q hq
    rw [← equations_agree] at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    rw [interpret_relabel, MvPolynomial.eval₂_rename]
    have heq : u ∘ Fin.val = x := by funext i; simp [u, i.isLt]
    rw [heq]
    exact hx p hp
  · rintro ⟨x, hx⟩
    apply (NumericSparseSource.satisfiable_iff s).mpr
    refine ⟨x ∘ Fin.val, ?_⟩
    intro p hp
    have h := hx (relabel Fin.val p) (by rw [← equations_agree]; exact List.mem_map.mpr ⟨p, hp, rfl⟩)
    simpa only [interpret_relabel, MvPolynomial.eval₂_rename] using h

def normalized (input : List Bool) : List (Poly ℕ) := equations (SourceSmallLiterals.normalizeSmall input)

theorem normalized_satisfiable_iff (input : List Bool) : input ∈ ETR ↔
    ∃ x : ℕ → ℝ, ∀ q ∈ normalized input, (interpret q).eval₂ (Int.castRingHom ℝ) x = 0 :=
  (SourceSmallLiterals.normalizeSmall_satisfiable input).symm.trans (satisfiable_iff _)

theorem normalized_raw_bound (input : List Bool) (q : Poly ℕ) (hq : q ∈ normalized input) :
    SparseCircuit.RawBound 5 q :=
  SparseCircuit.rawBound_mono (by have := SourceSmallLiterals.normalizeSmall_height input; omega) (raw_bound _ q hq)

end JointThermoComplexity.Complexity.NumberedSourceEquations

#print axioms JointThermoComplexity.Complexity.NumberedSourceEquations.equations_agree
#print axioms JointThermoComplexity.Complexity.NumberedSourceEquations.satisfiable_iff
#print axioms JointThermoComplexity.Complexity.NumberedSourceEquations.normalized_satisfiable_iff
