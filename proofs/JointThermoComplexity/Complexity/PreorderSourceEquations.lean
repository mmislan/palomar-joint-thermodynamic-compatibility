module
public import proofs.JointThermoComplexity.Complexity.PreorderFormulaEquations
public import proofs.JointThermoComplexity.Complexity.NumberedSourceEquations

set_option autoImplicit false
@[expose] public section

/-! Exact source semantics for the forward equation stream, via a proved permutation of accepted data. -/

namespace JointThermoComplexity.Complexity.PreorderSourceEquations
open RealSyntax SparseInteger SourceCoordinateEnumeration

def equations (s : Sentence) : List (Poly ℕ) := PreorderFormulaEquations.closed s.formula Fin.val s.arity

theorem perm_numbered (s : Sentence) : (equations s).Perm (NumberedSourceEquations.equations s) :=
  PreorderFormulaEquations.closed_perm s.formula Fin.val s.arity

theorem equation_count (s : Sentence) : (equations s).length = (NumericSparseSource.equations s).length :=
  (perm_numbered s).length_eq.trans (NumberedSourceEquations.equation_count s)

theorem equation_count_bound (s : Sentence) : (equations s).length ≤ 4 * s.code.length + 1 :=
  (perm_numbered s).length_eq.le.trans (NumberedSourceEquations.equation_count_bound s)

theorem coordinate_bound (s : Sentence) (q : Poly ℕ) (hq : q ∈ equations s) (a : ℤ × List ℕ) (ha : a ∈ q)
    (v : ℕ) (hv : v ∈ a.2) : v < sourceCount s :=
  NumberedSourceEquations.coordinate_bound s q ((perm_numbered s).mem_iff.mp hq) a ha v hv

theorem raw_bound (s : Sentence) (q : Poly ℕ) (hq : q ∈ equations s) :
    SparseCircuit.RawBound (3 + s.formula.literalHeight) q :=
  NumberedSourceEquations.raw_bound s q ((perm_numbered s).mem_iff.mp hq)

theorem satisfiable_iff (s : Sentence) : s.Satisfiable ↔
    ∃ x : ℕ → ℝ, ∀ q ∈ equations s, (interpret q).eval₂ (Int.castRingHom ℝ) x = 0 := by
  rw [NumberedSourceEquations.satisfiable_iff]
  apply exists_congr
  intro x
  constructor
  · intro h q hq
    exact h q ((perm_numbered s).mem_iff.mp hq)
  · intro h q hq
    exact h q ((perm_numbered s).mem_iff.mpr hq)

def normalized (input : List Bool) : List (Poly ℕ) := equations (SourceSmallLiterals.normalizeSmall input)

theorem normalized_satisfiable_iff (input : List Bool) : input ∈ ETR ↔
    ∃ x : ℕ → ℝ, ∀ q ∈ normalized input, (interpret q).eval₂ (Int.castRingHom ℝ) x = 0 :=
  (SourceSmallLiterals.normalizeSmall_satisfiable input).symm.trans (satisfiable_iff _)

theorem normalized_raw_bound (input : List Bool) (q : Poly ℕ) (hq : q ∈ normalized input) :
    SparseCircuit.RawBound 5 q :=
  SparseCircuit.rawBound_mono (by have := SourceSmallLiterals.normalizeSmall_height input; omega) (raw_bound _ q hq)

end JointThermoComplexity.Complexity.PreorderSourceEquations

#print axioms JointThermoComplexity.Complexity.PreorderSourceEquations.perm_numbered
#print axioms JointThermoComplexity.Complexity.PreorderSourceEquations.normalized_satisfiable_iff
