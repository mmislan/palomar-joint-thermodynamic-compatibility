module
public import proofs.JointThermoComplexity.Complexity.SparseCubeSemantics
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

set_option autoImplicit false
@[expose] public section

/-! Exact positive-coordinate witness domains for raw integer polynomials. -/

namespace JointThermoComplexity.Complexity.SparsePositiveCoordinates
open SparseInteger SparseSubstitution
variable {V W : Type}

def HalfCube (x : V → ℝ) : Prop := ∀ v, -(1 / 2 : ℝ) < x v ∧ x v < 1 / 2
def PositiveBox (p : Poly V) : Prop :=
  ∃ x : V → ℝ, (∀ v, 1 < x v ∧ x v < 2) ∧ 0 < (interpret p).eval₂ (Int.castRingHom ℝ) x
def PositiveOrthant (p : Poly V) : Prop :=
  ∃ x : V → ℝ, (∀ v, 0 < x v) ∧ 0 < (interpret p).eval₂ (Int.castRingHom ℝ) x

theorem cube_positive_iff (p : Poly V) (hp : DegreeLE 4 p) :
    (∃ x : V → ℝ, HalfCube x ∧ 0 < (interpret p).eval₂ (Int.castRingHom ℝ) x) ↔
      PositiveBox (cube 4 p) := by
  constructor
  · rintro ⟨x, hx, hpos⟩
    refine ⟨fun v => x v + 3 / 2, ?_, ?_⟩
    · intro v
      constructor <;> linarith [(hx v).1, (hx v).2]
    · rw [eval_cube 4 p hp]
      have he : (fun v => x v + 3 / 2 - 3 / 2) = x := by funext v; ring
      rw [he]
      exact mul_pos (by norm_num) hpos
  · rintro ⟨x, hx, hpos⟩
    refine ⟨fun v => x v - 3 / 2, ?_, ?_⟩
    · intro v
      constructor <;> linarith [(hx v).1, (hx v).2]
    · rw [eval_cube 4 p hp] at hpos
      exact (mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 2 ^ 4)).mp hpos

theorem orthant_positive_iff (p : Poly V) :
    (∃ x : V → ℝ, 0 < (interpret p).eval₂ (Int.castRingHom ℝ) x) ↔ PositiveOrthant (orthant p) := by
  constructor
  · rintro ⟨x, hpos⟩
    let u : V ⊕ V → ℝ := Sum.elim (fun v => x v + |x v| + 1) (fun v => |x v| + 1)
    refine ⟨u, ?_, ?_⟩
    · intro v
      cases v with
      | inl v => have h := neg_abs_le (x v); dsimp [u]; linarith
      | inr v => dsimp [u]; positivity
    · rw [eval_orthant]
      have he : (fun v => u (.inl v) - u (.inr v)) = x := by funext v; dsimp [u]; ring
      rw [he]
      exact hpos
  · rintro ⟨x, _hx, hpos⟩
    exact ⟨fun v => x (.inl v) - x (.inr v), by simpa only [eval_orthant] using hpos⟩

theorem orthant_relabel (e : V ≃ W) (p : Poly V) :
    PositiveOrthant p ↔ PositiveOrthant (relabel e p) := by
  constructor
  · rintro ⟨x, hx, hpos⟩
    refine ⟨x ∘ e.symm, (fun v => hx (e.symm v)), ?_⟩
    simpa only [interpret_relabel, MvPolynomial.eval₂_rename, Function.comp_def,
      Equiv.symm_apply_apply] using hpos
  · rintro ⟨x, hx, hpos⟩
    refine ⟨x ∘ e, (fun v => hx (e v)), ?_⟩
    simpa only [interpret_relabel, MvPolynomial.eval₂_rename] using hpos

end JointThermoComplexity.Complexity.SparsePositiveCoordinates

#print axioms JointThermoComplexity.Complexity.SparsePositiveCoordinates.cube_positive_iff
#print axioms JointThermoComplexity.Complexity.SparsePositiveCoordinates.orthant_positive_iff
#print axioms JointThermoComplexity.Complexity.SparsePositiveCoordinates.orthant_relabel
