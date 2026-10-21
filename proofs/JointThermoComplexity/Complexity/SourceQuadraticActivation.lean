module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/- Adapted from DInstabilityComplexity/QuadraticActivation.lean in the private
D-stability completeness development. Original source and SHA-256 are
preserved in SOURCE_QUADRATIC_CIRCUIT_ADAPTATION.json and syntax-inputs/.
The original package Apache-2.0 license is retained in
third_party/quadratic-witness/LICENSE.original. This version uses only
the independently defined RealSyntax; no source-hardness theorem is assumed. -/

/-! # Quadratic activation and strict-sign witnesses for formula atoms

An inactive atom imposes no condition on its input values. An active strict
inequality is enforced by d*y^2=1, split into quadratic operation equations.
-/

namespace JointThermoComplexity.Complexity.QuadraticCircuit

variable {n : ℕ} {V W : Type}

def BooleanBit (a : ℝ) : Prop := a * (a - 1) = 0

theorem booleanBit_iff (a : ℝ) : BooleanBit a ↔ a = 0 ∨ a = 1 := by
  simp only [BooleanBit, mul_eq_zero, sub_eq_zero]

def EqualityActivation (a l r : ℝ) : Prop := BooleanBit a ∧ a * (l - r) = 0

theorem equalityActivation_iff (a l r : ℝ) :
    EqualityActivation a l r ↔ BooleanBit a ∧ (a = 0 ∨ l = r) := by
  simp only [EqualityActivation, mul_eq_zero, sub_eq_zero]

def StrictSignActivation (a l r y b c : ℝ) : Prop :=
  BooleanBit a ∧ b = y ^ 2 ∧ c = (r - l) * b ∧ a * (c - 1) = 0

theorem strictSignActivation_sound {a l r y b c : ℝ} (h : StrictSignActivation a l r y b c) :
    BooleanBit a ∧ (a = 0 ∨ l < r) := by
  refine ⟨h.1, ?_⟩
  rcases mul_eq_zero.mp h.2.2.2 with ha | hc
  · exact Or.inl ha
  · right
    have hc1 : c = 1 := sub_eq_zero.mp hc
    have he : (r - l) * y ^ 2 = 1 := by rw [← h.2.1, ← h.2.2.1, hc1]
    by_contra! hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hn) (sq_nonneg y)
    linarith only [he, hm]

theorem strictSignActivation_extension (a l r : ℝ) (ha : BooleanBit a) (h : a = 0 ∨ l < r) :
    ∃ y b c : ℝ, StrictSignActivation a l r y b c := by
  rcases h with hzero | hlt
  · subst a
    exact ⟨0, 0, 0, by norm_num [StrictSignActivation, BooleanBit]⟩
  · let d := r - l
    have hd : 0 < d := sub_pos.mpr hlt
    refine ⟨(Real.sqrt d)⁻¹, d⁻¹, 1, ha, ?_, ?_, ?_⟩
    · rw [inv_pow, Real.sq_sqrt hd.le]
    · exact (mul_inv_cancel₀ (ne_of_gt hd)).symm
    · simp

theorem strictSignActivation_iff (a l r : ℝ) :
    (∃ y b c : ℝ, StrictSignActivation a l r y b c) ↔ BooleanBit a ∧ (a = 0 ∨ l < r) := by
  constructor
  · rintro ⟨y, b, c, h⟩
    exact strictSignActivation_sound h
  · rintro ⟨ha, h⟩
    exact strictSignActivation_extension a l r ha h

def DisjunctionPartition (a b c : ℝ) : Prop := BooleanBit b ∧ BooleanBit c ∧ b + c = a

theorem disjunctionPartition_iff {a b c : ℝ} (ha : BooleanBit a) :
    DisjunctionPartition a b c ↔
      (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 1 ∧ b = 1 ∧ c = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 1) := by
  constructor
  · rintro ⟨hb, hc, he⟩
    rcases (booleanBit_iff a).mp ha with ha | ha <;>
      rcases (booleanBit_iff b).mp hb with hb | hb <;>
      rcases (booleanBit_iff c).mp hc with hc | hc <;>
      simp_all
  · intro h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      norm_num [DisjunctionPartition, BooleanBit]

#print axioms booleanBit_iff
#print axioms equalityActivation_iff
#print axioms strictSignActivation_iff
#print axioms disjunctionPartition_iff

end JointThermoComplexity.Complexity.QuadraticCircuit
