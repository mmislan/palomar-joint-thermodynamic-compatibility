module
public import proofs.JointThermoComplexity.Complexity.SourceClosedQuadratic
public import proofs.JointThermoComplexity.Complexity.QuadraticWitnessBridge

set_option autoImplicit false
@[expose] public section

/-! # One effectively bounded quadratic witness for each satisfiable source sentence

The source formula and its quadratic normal form were defined independently
of the chemistry. The bound is derived from feasibility, not supplied as an
algebraic certificate. A scale here is a mathematical parameter; no expansion
of the coordinate height or polynomial-time bit emitter is asserted.
-/

namespace JointThermoComplexity.Complexity.QuadraticCircuit
open RealSyntax

noncomputable def sourceHeight (s : Sentence) : ℕ :=
  QuadraticWitnessBridge.height (sourceEquations s)

theorem source_satisfiable_iff_effectively_bounded (s : Sentence) :
    s.Satisfiable ↔ ∃ x : Fin (sourceArity s) → ℝ,
      EquationsHold (sourceEquations s) x ∧ ∀ i, |x i| < (sourceHeight s : ℝ) + 1 := by
  constructor
  · intro hs
    exact QuadraticWitnessBridge.exists_effectively_bounded (sourceEquations s)
      (sourceEquations_quadratic s) ((sourceEquations_satisfiable_iff s).mpr hs)
  · rintro ⟨x, hx, _⟩
    exact (sourceEquations_satisfiable_iff s).mp ⟨x, hx⟩

theorem source_satisfiable_iff_common_scaled (s : Sentence) (scale : ℝ) (hpos : 0 < scale)
    (hsmall : scale * ((sourceHeight s : ℝ) + 1) ≤ 1 / 2) :
    s.Satisfiable ↔ ∃ u : Fin (sourceArity s) → ℝ,
      (∀ i, -(1 / 2 : ℝ) < u i ∧ u i < 1 / 2) ∧
        EquationsHold (sourceEquations s) (fun i => u i / scale) := by
  constructor
  · intro hs
    exact QuadraticWitnessBridge.exists_common_scaled_witness (sourceEquations s)
      (sourceEquations_quadratic s) ((sourceEquations_satisfiable_iff s).mpr hs)
      scale hpos hsmall
  · rintro ⟨u, _, hu⟩
    exact (sourceEquations_satisfiable_iff s).mp ⟨fun i => u i / scale, hu⟩

end JointThermoComplexity.Complexity.QuadraticCircuit

#print axioms JointThermoComplexity.Complexity.QuadraticCircuit.source_satisfiable_iff_effectively_bounded
#print axioms JointThermoComplexity.Complexity.QuadraticCircuit.source_satisfiable_iff_common_scaled
