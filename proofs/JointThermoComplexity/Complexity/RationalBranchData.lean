module
public import proofs.JointThermoComplexity.EmittedSource

set_option autoImplicit false
@[expose] public section

/-! Executable positive rational branch factors and natural exponent arrays.
Their real interpretation is separate from the stored input data. -/

namespace JointThermoComplexity.Complexity.RationalBranchData
variable {E : Type} {n : ℕ}

structure Data (E : Type) (n : ℕ) where
  numerator : Fin (n + 1) → ℕ
  denominator : Fin (n + 1) → ℕ
  numerator_pos : ∀ i, 0 < numerator i
  denominator_pos : ∀ i, 0 < denominator i
  exponent : Fin (n + 1) → E → ℕ

def Data.numeratorAt (b : Data E n) (i : Fin (n + 2)) : ℕ :=
  if h : i.val = 0 then 1 else b.numerator ⟨i.val - 1, by omega⟩

def Data.denominatorAt (b : Data E n) (i : Fin (n + 2)) : ℕ :=
  if h : i.val = 0 then 1 else b.denominator ⟨i.val - 1, by omega⟩

def Data.powers (b : Data E n) (i : Fin (n + 2)) (e : E) : ℕ :=
  if h : i.val = 0 then 0 else b.exponent ⟨i.val - 1, by omega⟩ e

theorem Data.numeratorAt_pos (b : Data E n) (i : Fin (n + 2)) : 0 < b.numeratorAt i := by
  unfold Data.numeratorAt
  split_ifs
  · decide
  · exact b.numerator_pos _

theorem Data.denominatorAt_pos (b : Data E n) (i : Fin (n + 2)) : 0 < b.denominatorAt i := by
  unfold Data.denominatorAt
  split_ifs
  · decide
  · exact b.denominator_pos _

noncomputable def Data.toBranch (b : Data E n) : Emitted.Branch E n where
  coefficient i := (b.denominator i : ℝ) / b.numerator i
  coefficient_pos i := div_pos (by exact_mod_cast b.denominator_pos i) (by exact_mod_cast b.numerator_pos i)
  exponent := b.exponent

theorem Data.powers_eq (b : Data E n) (i : Fin (n + 2)) (e : E) :
    b.powers i e = b.toBranch.powers i e := rfl

theorem Data.barrier_eq (b : Data E n) (i : Fin (n + 2)) :
    b.toBranch.barrier i = (b.numeratorAt i : ℝ) / b.denominatorAt i := by
  unfold Emitted.Branch.barrier Data.numeratorAt Data.denominatorAt Data.toBranch
  split_ifs
  · norm_num
  · rw [one_div_div]

theorem Data.factor_bounds (b : Data E n) (hb : ∀ i, b.numerator i ≤ 2) (i : Fin (n + 2)) :
    0 < (b.numeratorAt i : ℝ) / b.denominatorAt i ∧ (b.numeratorAt i : ℝ) / b.denominatorAt i ≤ 2 := by
  have hn : b.numeratorAt i ≤ 2 := by
    unfold Data.numeratorAt
    split_ifs
    · decide
    · exact hb _
  have hnr : (0 : ℝ) < b.numeratorAt i := by exact_mod_cast b.numeratorAt_pos i
  have hdr : (0 : ℝ) < b.denominatorAt i := by exact_mod_cast b.denominatorAt_pos i
  have hn2 : (b.numeratorAt i : ℝ) ≤ 2 := by exact_mod_cast hn
  have hd1 : (1 : ℝ) ≤ b.denominatorAt i := by exact_mod_cast b.denominatorAt_pos i
  exact ⟨div_pos hnr hdr, (div_le_iff₀ hdr).mpr (by linarith)⟩

end JointThermoComplexity.Complexity.RationalBranchData

#print axioms JointThermoComplexity.Complexity.RationalBranchData.Data.numeratorAt
#print axioms JointThermoComplexity.Complexity.RationalBranchData.Data.denominatorAt
#print axioms JointThermoComplexity.Complexity.RationalBranchData.Data.barrier_eq
#print axioms JointThermoComplexity.Complexity.RationalBranchData.Data.factor_bounds
