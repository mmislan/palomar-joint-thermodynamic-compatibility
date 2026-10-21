module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity

theorem intervals_overlap_iff (L R : ℝ) :
    (∃ q : ℝ, L/2 < q ∧ q < L ∧ R/2 < q ∧ q < R) ↔
    (0 < L ∧ 0 < R ∧ L < 2*R ∧ R < 2*L) := by
  constructor
  · rintro ⟨q, h₁, h₂, h₃, h₄⟩
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨hL, hR, hLR, hRL⟩
    have h : max (L/2) (R/2) < min L R := by
      apply max_lt
      · exact lt_min (by linarith) (by linarith)
      · exact lt_min (by linarith) (by linarith)
    obtain ⟨q, hq₁, hq₂⟩ := exists_between h
    exact ⟨q, lt_of_le_of_lt (le_max_left _ _) hq₁,
      lt_of_lt_of_le hq₂ (min_le_left _ _),
      lt_of_le_of_lt (le_max_right _ _) hq₁,
      lt_of_lt_of_le hq₂ (min_le_right _ _)⟩

theorem offset_comparator (K P Q : ℝ) (hK : 0 < K)
    (hP : 0 ≤ P) :
    (∃ q : ℝ, (K+P)/2 < q ∧ q < K+P ∧
      ((K+Q)/2)/2 < q ∧ q < (K+Q)/2) ↔
    (P < Q ∧ Q < 3*K+4*P) := by
  rw [intervals_overlap_iff]
  constructor
  · rintro ⟨_, _, h₁, h₂⟩
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

end JointThermoComplexity

#print axioms JointThermoComplexity.intervals_overlap_iff

#print axioms JointThermoComplexity.offset_comparator
