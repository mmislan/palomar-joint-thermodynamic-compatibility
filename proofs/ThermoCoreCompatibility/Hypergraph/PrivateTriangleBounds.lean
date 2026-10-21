module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Tauto

set_option autoImplicit false
@[expose] public section

namespace ThermoCoreCompatibility.Hypergraph

/-- Intersect two strict lower bounds and one strict upper bound with a closed box.
The box may be a singleton. -/
theorem private_interval_box_iff {a b c l u : ℝ} (hlu : l ≤ u) :
    (∃ x, l ≤ x ∧ x ≤ u ∧ a < x ∧ b < x ∧ x < c) ↔
      a < c ∧ b < c ∧ l < c ∧ a < u ∧ b < u := by
  constructor
  · rintro ⟨x, hl, hu, ha, hb, hc⟩
    exact ⟨lt_trans ha hc, lt_trans hb hc, lt_of_le_of_lt hl hc,
      lt_of_lt_of_le ha hu, lt_of_lt_of_le hb hu⟩
  · rintro ⟨hac, hbc, hlc, hau, hbu⟩
    by_cases h : max a b < l
    · exact ⟨l, le_rfl, hlu, lt_of_le_of_lt (le_max_left a b) h,
        lt_of_le_of_lt (le_max_right a b) h, hlc⟩
    · have hl : l ≤ max a b := le_of_not_gt h
      have hmc : max a b < c := max_lt hac hbc
      have hmu : max a b < u := max_lt hau hbu
      let x := min u ((max a b + c) / 2)
      have hx : max a b < x := by
        dsimp [x]
        exact lt_min hmu (by linarith)
      have hxc : x < c := by
        have hh := min_le_right u ((max a b + c) / 2)
        dsimp [x]
        linarith
      exact ⟨x, le_trans hl (le_of_lt hx), min_le_left _ _,
        lt_of_le_of_lt (le_max_left a b) hx,
        lt_of_le_of_lt (le_max_right a b) hx, hxc⟩

/-- Literal triangle production, with one fixed shared current. -/
def TriangleProduction (m b₁ b₂ A B C j : ℝ) : Prop :=
  j < m * (b₂ * (C - A)) ∧ b₁ * (B - C) < j ∧
    b₂ * (C - A) < b₁ * (B - C)

/-- Here A denotes the terminal complex activity (later specialized to a^m).
This elementary elimination does not assume an independent physical lift. -/
theorem triangleProduction_iff_bounds {m b₁ b₂ A B C j : ℝ}
    (hm : 0 < m) (h₁ : 0 < b₁) (h₂ : 0 < b₂) :
    TriangleProduction m b₁ b₂ A B C j ↔
      B - j / b₁ < C ∧ A + j / (m * b₂) < C ∧
        C < (b₁ * B + b₂ * A) / (b₁ + b₂) := by
  have hp : 0 < m * b₂ := mul_pos hm h₂
  have hs : 0 < b₁ + b₂ := add_pos h₁ h₂
  have hlow₁ : B - j / b₁ < C ↔ b₁ * (B - C) < j := by
    rw [sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_div_iff₀ h₁]
    constructor <;> intro h <;> nlinarith
  have hlow₂ : A + j / (m * b₂) < C ↔ j < m * (b₂ * (C - A)) := by
    rw [add_comm A, ← lt_sub_iff_add_lt, div_lt_iff₀ hp]
    constructor <;> intro h <;> nlinarith
  have hu : C < (b₁ * B + b₂ * A) / (b₁ + b₂) ↔
      b₂ * (C - A) < b₁ * (B - C) := by
    rw [lt_div_iff₀ hs]
    constructor <;> intro h <;> nlinarith
  rw [hlow₁, hlow₂, hu]
  unfold TriangleProduction
  tauto

theorem privateTriangle_box_iff {m b₁ b₂ A B j l u : ℝ}
    (hm : 0 < m) (h₁ : 0 < b₁) (h₂ : 0 < b₂) (hlu : l ≤ u) :
    (∃ C, l ≤ C ∧ C ≤ u ∧ TriangleProduction m b₁ b₂ A B C j) ↔
      B - j / b₁ < (b₁ * B + b₂ * A) / (b₁ + b₂) ∧
      A + j / (m * b₂) < (b₁ * B + b₂ * A) / (b₁ + b₂) ∧
      l < (b₁ * B + b₂ * A) / (b₁ + b₂) ∧
      B - j / b₁ < u ∧ A + j / (m * b₂) < u := by
  simp_rw [triangleProduction_iff_bounds hm h₁ h₂]
  exact private_interval_box_iff hlu

/-- Denominator-free form, suitable for exact polynomial sign certificates. -/
theorem privateTriangle_box_iff_polynomial {m b₁ b₂ A B j l u : ℝ}
    (hm : 0 < m) (h₁ : 0 < b₁) (h₂ : 0 < b₂) (hlu : l ≤ u) :
    (∃ C, l ≤ C ∧ C ≤ u ∧ TriangleProduction m b₁ b₂ A B C j) ↔
      b₁ * b₂ * (B - A) < (b₁ + b₂) * j ∧
      (b₁ + b₂) * j < m * b₁ * b₂ * (B - A) ∧
      (b₁ + b₂) * l < b₁ * B + b₂ * A ∧
      b₁ * B - j < b₁ * u ∧ m * b₂ * A + j < m * b₂ * u := by
  rw [privateTriangle_box_iff hm h₁ h₂ hlu]
  have hp : 0 < m * b₂ := mul_pos hm h₂
  have hs : 0 < b₁ + b₂ := add_pos h₁ h₂
  have e₁ : B - j / b₁ = (b₁ * B - j) / b₁ := by
    field_simp
  have e₂ : A + j / (m * b₂) = (m * b₂ * A + j) / (m * b₂) := by
    field_simp
  rw [e₁, e₂, div_lt_div_iff₀ h₁ hs, div_lt_div_iff₀ hp hs,
    lt_div_iff₀ hs, div_lt_iff₀ h₁, div_lt_iff₀ hp]
  constructor <;> rintro ⟨ha, hb, hc, hd, he⟩ <;>
    constructor <;> try nlinarith
  · exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end ThermoCoreCompatibility.Hypergraph

#print axioms ThermoCoreCompatibility.Hypergraph.privateTriangle_box_iff_polynomial
