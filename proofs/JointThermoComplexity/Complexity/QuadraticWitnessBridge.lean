module
public import proofs.DInstabilityComplexity.QuadraticWitnessBound

set_option autoImplicit false
@[expose] public section

/-! Finite-list quadratic systems inherit the proved common witness bound and a shared positive-scale margin.
The imported effective mathematics is preserved byte-for-byte with its original module names and receipts.
No bounded witness is supplied as an input certificate. -/

namespace JointThermoComplexity.Complexity.QuadraticWitnessBridge

variable {n : ℕ}

def Holds (qs : List (MvPolynomial (Fin n) ℤ)) (x : Fin n → ℝ) : Prop :=
  ∀ q ∈ qs, q.eval₂ (Int.castRingHom ℝ) x = 0

def family (qs : List (MvPolynomial (Fin n) ℤ)) (j : Fin qs.length) : MvPolynomial (Fin n) ℤ := qs[j.val]'j.isLt

theorem holds_iff_family (qs : List (MvPolynomial (Fin n) ℤ)) (x : Fin n → ℝ) :
    Holds qs x ↔ ∀ j, (family qs j).eval₂ (Int.castRingHom ℝ) x = 0 := by
  constructor
  · intro hx j
    exact hx _ (List.getElem_mem j.isLt)
  · intro hx
    exact List.forall_mem_iff_getElem.mpr (fun i hi => hx ⟨i, hi⟩)

noncomputable def height (qs : List (MvPolynomial (Fin n) ℤ)) : ℕ :=
  DInstabilityComplexity.Separation.quadraticCoordinateHeight n
    (DInstabilityComplexity.Separation.quadraticCriticalLength (family qs))

theorem exists_effectively_bounded (qs : List (MvPolynomial (Fin n) ℤ))
    (hq : ∀ q ∈ qs, q.totalDegree ≤ 2) (hf : ∃ x, Holds qs x) :
    ∃ x : Fin n → ℝ, Holds qs x ∧ ∀ i, |x i| < (height qs : ℝ) + 1 := by
  classical
  obtain ⟨w, hw⟩ := hf
  have hdegree : ∀ j, (family qs j).totalDegree ≤ 2 := fun j => hq _ (List.getElem_mem j.isLt)
  obtain ⟨x, hx, hb⟩ := DInstabilityComplexity.Separation.exists_effectively_bounded_quadratic_solution
    (family qs) hdegree ⟨w, (holds_iff_family qs w).mp hw⟩
  exact ⟨x, (holds_iff_family qs x).mpr hx, by simpa only [height, Fintype.card_fin] using hb⟩

theorem exists_common_scaled_witness (qs : List (MvPolynomial (Fin n) ℤ))
    (hq : ∀ q ∈ qs, q.totalDegree ≤ 2) (hf : ∃ x, Holds qs x) (s : ℝ) (hs : 0 < s)
    (hsmall : s * ((height qs : ℝ) + 1) ≤ 1 / 2) :
    ∃ u : Fin n → ℝ, (∀ i, -(1 / 2 : ℝ) < u i ∧ u i < 1 / 2) ∧ Holds qs (fun i => u i / s) := by
  obtain ⟨x, hx, hb⟩ := exists_effectively_bounded qs hq hf
  let u : Fin n → ℝ := fun i => s * x i
  have he : (fun i => u i / s) = x := by
    funext i
    simp [u, ne_of_gt hs]
  refine ⟨u, ?_, by rw [he]; exact hx⟩
  intro i
  have hu : |u i| < s * ((height qs : ℝ) + 1) := by
    simpa only [u, abs_mul, abs_of_pos hs] using mul_lt_mul_of_pos_left (hb i) hs
  exact abs_lt.mp (hu.trans_le hsmall)

end JointThermoComplexity.Complexity.QuadraticWitnessBridge

#print axioms JointThermoComplexity.Complexity.QuadraticWitnessBridge.exists_effectively_bounded
#print axioms JointThermoComplexity.Complexity.QuadraticWitnessBridge.exists_common_scaled_witness
