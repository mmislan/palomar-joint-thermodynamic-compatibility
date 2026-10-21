module
public import proofs.JointThermoComplexity.Complexity.StrictRawBounds

set_option autoImplicit false
@[expose] public section

/-! Bounds on each stored coefficient survive concatenation without depending
on the number of equations. No polynomial cancellation is used. -/

namespace JointThermoComplexity.Complexity.SparseInteger
variable {V W : Type}

def CoefficientsLE (B : ℕ) (p : Poly V) : Prop := ∀ a ∈ p, a.1.natAbs ≤ B

theorem coefficients_of_weight {B : ℕ} {p : Poly V} (h : rawWeight p ≤ B) : CoefficientsLE B p :=
  fun a ha => Nat.le_trans (rawWeight_member p a ha) h

theorem coefficients_mono {A B : ℕ} {p : Poly V} (hAB : A ≤ B) (h : CoefficientsLE A p) :
    CoefficientsLE B p := fun a ha => Nat.le_trans (h a ha) hAB

theorem coefficients_add {B : ℕ} {p q : Poly V} (hp : CoefficientsLE B p) (hq : CoefficientsLE B q) :
    CoefficientsLE B (add p q) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hp a ha
  · exact hq a ha

theorem coefficients_scale (c : ℤ) {B : ℕ} {p : Poly V} (hp : CoefficientsLE B p) :
    CoefficientsLE (c.natAbs * B) (scale c p) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  change (c * b.1).natAbs ≤ c.natAbs * B
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul_left _ (hp b hb)

theorem coefficients_neg {B : ℕ} {p : Poly V} (hp : CoefficientsLE B p) : CoefficientsLE B (neg p) := by
  simpa only [neg, Int.natAbs_neg, Int.natAbs_one, Nat.one_mul] using coefficients_scale (-1) hp

theorem coefficients_sub {B : ℕ} {p q : Poly V} (hp : CoefficientsLE B p) (hq : CoefficientsLE B q) :
    CoefficientsLE B (sub p q) := coefficients_add hp (coefficients_neg hq)

theorem coefficients_relabel (f : V → W) {B : ℕ} {p : Poly V} (hp : CoefficientsLE B p) :
    CoefficientsLE B (relabel f p) := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact hp b hb

end JointThermoComplexity.Complexity.SparseInteger

namespace JointThermoComplexity.Complexity.SparseStrictPolynomial
open SparseInteger
variable {V : Type} {n : ℕ}

theorem sumFamily_coefficients (q : Fin n → Poly V) (B : ℕ) (hq : ∀ j, CoefficientsLE B (q j)) :
    CoefficientsLE B (sumFamily q) := by
  intro a ha
  obtain ⟨p, hp, ha⟩ := List.mem_flatten.mp ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  exact hq j a ha

theorem energy_coefficients (q : Fin n → Poly V) (B : ℕ) (hq : ∀ j, rawWeight (q j) ≤ B) :
    CoefficientsLE (B ^ 2) (energy q) := by
  apply sumFamily_coefficients
  intro j
  apply coefficients_of_weight
  rw [rawWeight_square]
  exact Nat.pow_le_pow_left (hq j) 2

theorem error_coefficients (k : ℕ) : CoefficientsLE 1024 (error k) := by
  exact energy_coefficients (edge k) 32 (edge_weight k)

theorem bounded_fixed_coefficients (q : Fin n → Poly V) (k : ℕ) (hq : ∀ j, rawWeight (q j) ≤ 33) :
    CoefficientsLE 409600 (bounded q k) := by
  apply coefficients_sub
  · apply coefficients_sub
    · apply coefficients_of_weight
      simp
    · have h := coefficients_scale 256 (coefficients_relabel (Sum.inl : V → V ⊕ Fin (k + 1)) (energy_coefficients q 33 hq))
      exact coefficients_mono (by decide : 256 * 33 ^ 2 ≤ 409600) h
  · exact coefficients_scale 400 (coefficients_relabel Sum.inr (error_coefficients k))

theorem allReal_fixed_coefficients (q : Fin n → Poly V) (k : ℕ) (hq : ∀ j, rawWeight (q j) ≤ 33) :
    CoefficientsLE 409600 (allReal q k) := by
  apply coefficients_sub
  · apply coefficients_sub
    · apply coefficients_of_weight
      simp
    · have h := coefficients_scale 256 (coefficients_relabel (Sum.inl : V → V ⊕ Fin (k + 1)) (energy_coefficients q 33 hq))
      exact coefficients_mono (by decide : 256 * 33 ^ 2 ≤ 409600) h
  · exact coefficients_scale 400 (coefficients_relabel Sum.inr (error_coefficients k))

end JointThermoComplexity.Complexity.SparseStrictPolynomial

#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.energy_coefficients
#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.bounded_fixed_coefficients
#print axioms JointThermoComplexity.Complexity.SparseStrictPolynomial.allReal_fixed_coefficients
