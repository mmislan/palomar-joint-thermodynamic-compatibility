module
public import proofs.DInstabilityComplexity.SeparationRoot

@[expose] public section

/-! # An upper bound for every real root of a nonzero integer polynomial -/

namespace DInstabilityComplexity.Separation

noncomputable section

theorem integer_root_abs_lt_height_add_one (p : Polynomial ℤ) (hp : p ≠ 0) (H : ℕ)
    (hc : ∀ j, (p.coeff j).natAbs ≤ H) (a : ℝ)
    (hroot : p.eval₂ (Int.castRingHom ℝ) a = 0) : |a| < (H : ℝ) + 1 := by
  let q := p.map (Int.castRingHom ℝ)
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  have hcoef : ∀ j, ‖q.coeff j‖₊ ≤ (H : NNReal) := by
    intro j
    apply NNReal.coe_le_coe.mp
    change ‖q.coeff j‖ ≤ (H : ℝ)
    rw [show q.coeff j = ((p.coeff j : ℤ) : ℝ) by simp [q], Real.norm_eq_abs]
    have hZ : |p.coeff j| ≤ (H : ℤ) := by
      have hN : ((p.coeff j).natAbs : ℤ) ≤ (H : ℤ) := by exact_mod_cast hc j
      simpa only [Int.natCast_natAbs] using hN
    exact_mod_cast hZ
  have hlc : 1 ≤ ‖q.leadingCoeff‖₊ := by
    change 1 ≤ ‖(p.map (Int.castRingHom ℝ)).leadingCoeff‖₊
    rw [Polynomial.leadingCoeff_map_of_injective (f := Int.castRingHom ℝ) Int.cast_injective]
    exact one_le_norm_intCast _ (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hr : q.IsRoot a := by
    rw [Polynomial.IsRoot.def]
    change (p.map (Int.castRingHom ℝ)).eval a = 0
    rw [Polynomial.eval_map]
    exact hroot
  have hb := (hr.norm_lt_cauchyBound hq).trans_le (cauchyBound_le_of_coeff_bound q H hcoef hlc)
  have hreal : ‖a‖ < (H : ℝ) + 1 := by exact_mod_cast hb
  simpa only [Real.norm_eq_abs] using hreal

#print axioms integer_root_abs_lt_height_add_one

end
end DInstabilityComplexity.Separation
