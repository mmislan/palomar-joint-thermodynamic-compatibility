module
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Quantitative separation of nonzero integer-polynomial roots

This is the numerical last step of an effective elimination argument. It is
proved from Mathlib's Cauchy bound, including polynomials with zero constant
coefficient. Constructing a bounded integer eliminant for the torus minimum is
a separate obligation; this module does not assume or assert that construction.
-/

namespace DInstabilityComplexity.Separation

open Polynomial NNReal

noncomputable section

theorem cauchyBound_le_of_coeff_bound (p : ℝ[X]) (H : ℝ≥0)
    (hc : ∀ i, ‖p.coeff i‖₊ ≤ H) (hl : 1 ≤ ‖p.leadingCoeff‖₊) :
    p.cauchyBound ≤ H + 1 := by
  have hlpos : 0 < ‖p.leadingCoeff‖₊ := lt_of_lt_of_le zero_lt_one hl
  have hsup : (Finset.range p.natDegree).sup (fun i => ‖p.coeff i‖₊) ≤ H :=
    Finset.sup_le fun i _ => hc i
  have hd : (Finset.range p.natDegree).sup (fun i => ‖p.coeff i‖₊) /
      ‖p.leadingCoeff‖₊ ≤ H := by
    apply (div_le_iff₀ hlpos).mpr
    exact hsup.trans (le_mul_of_one_le_right (by positivity) hl)
  change _ / ‖p.leadingCoeff‖₊ + 1 ≤ H + 1
  exact add_le_add hd le_rfl

theorem one_le_norm_intCast (z : ℤ) (hz : z ≠ 0) :
    (1 : ℝ≥0) ≤ ‖(z : ℝ)‖₊ := by
  have h : 1 ≤ z.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hz)
  have hc : (1 : ℝ≥0) ≤ (z.natAbs : ℝ≥0) := by exact_mod_cast h
  simpa only [NNReal.natCast_natAbs, ← NNReal.coe_le_coe,
    coe_nnnorm, Int.norm_cast_real] using hc

/-- A height bound separates every nonzero real root from zero, even when zero
is also a root. Reversing the polynomial removes the need to divide out powers
of `X` explicitly. -/
theorem integer_root_abs_gt (p : ℤ[X]) (hp : p ≠ 0) (H : ℕ)
    (hH : ∀ i, |p.coeff i| ≤ (H : ℤ)) (a : ℝ) (ha : a ≠ 0)
    (hroot : p.eval₂ (Int.castRingHom ℝ) a = 0) :
    1 / ((H : ℝ) + 1) < |a| := by
  let q : ℝ[X] := p.reverse.map (Int.castRingHom ℝ)
  have hrev : p.reverse ≠ 0 := by simpa only [ne_eq, reverse_eq_zero] using hp
  have hq : q ≠ 0 := (Polynomial.map_ne_zero_iff (Int.cast_injective)).mpr hrev
  have hcoef : ∀ i, ‖q.coeff i‖₊ ≤ (H : ℝ≥0) := by
    intro i
    apply NNReal.coe_le_coe.mp
    change ‖q.coeff i‖ ≤ (H : ℝ)
    rw [show q.coeff i = ((p.reverse.coeff i : ℤ) : ℝ) by simp [q],
      Real.norm_eq_abs, coeff_reverse]
    exact_mod_cast hH (revAt p.natDegree i)
  have hlc : 1 ≤ ‖q.leadingCoeff‖₊ := by
    have h := one_le_norm_intCast p.reverse.leadingCoeff (leadingCoeff_ne_zero.mpr hrev)
    change 1 ≤ ‖(p.reverse.map (Int.castRingHom ℝ)).leadingCoeff‖₊
    rw [leadingCoeff_map_of_injective (f := Int.castRingHom ℝ) Int.cast_injective]
    exact h
  have hcb := cauchyBound_le_of_coeff_bound q H hcoef hlc
  have hr : q.IsRoot a⁻¹ := by
    let _ : Invertible a := invertibleOfNonzero ha
    rw [Polynomial.IsRoot.def]
    change (p.reverse.map (Int.castRingHom ℝ)).eval a⁻¹ = 0
    rw [eval_map]
    simpa only [invOf_eq_inv] using
      (eval₂_reverse_eq_zero_iff (Int.castRingHom ℝ) a p).mpr hroot
  have hinv : |a|⁻¹ < (H : ℝ) + 1 := by
    have h := lt_of_lt_of_le (hr.norm_lt_cauchyBound hq) hcb
    have hreal : ‖a⁻¹‖ < (H : ℝ) + 1 := by exact_mod_cast h
    simpa only [norm_inv, Real.norm_eq_abs] using hreal
  have hapos : 0 < |a| := abs_pos.mpr ha
  have hHpos : 0 < (H : ℝ) + 1 := by positivity
  apply (div_lt_iff₀ hHpos).mpr
  have h := mul_lt_mul_of_pos_right hinv hapos
  rw [inv_mul_cancel₀ (ne_of_gt hapos)] at h
  nlinarith

/-- Integer coefficients strictly below a positive integer height `H` give the
clean reciprocal `1/H`; this form fits integer bounds on resultant heights. -/
theorem integer_root_abs_ge_of_strict_height (p : ℤ[X]) (hp : p ≠ 0)
    (H : ℕ) (hHpos : 0 < H) (hH : ∀ i, |p.coeff i| < (H : ℤ))
    (a : ℝ) (ha : a ≠ 0) (hroot : p.eval₂ (Int.castRingHom ℝ) a = 0) :
    1 / (H : ℝ) ≤ |a| := by
  have hc : ∀ i, |p.coeff i| ≤ ((H - 1 : ℕ) : ℤ) := by
    intro i
    have h := hH i
    have hcast : ((H - 1 : ℕ) : ℤ) = (H : ℤ) - 1 := by
      exact Int.natCast_pred_of_pos hHpos
    rw [hcast]
    omega
  have hb := integer_root_abs_gt p hp (H - 1) hc a ha hroot
  have hcast : ((H - 1 : ℕ) : ℝ) + 1 = (H : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hHpos
  rw [hcast] at hb
  exact hb.le

#print axioms integer_root_abs_gt
#print axioms integer_root_abs_ge_of_strict_height

end
end DInstabilityComplexity.Separation
