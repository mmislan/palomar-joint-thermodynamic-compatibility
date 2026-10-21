module
public import proofs.JointThermoComplexity.EmittedCompatibility

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity.Emitted
open scoped BigOperators
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}

/-- Sparse polynomials allow arbitrary signed real coefficients; the complexity
application specializes these to rationals. Repeated monomials are allowed. -/
def polynomial (c : Fin n→ℝ) (γ : Fin n→E→ℕ) (v : E→ℝ) : ℝ :=
  ∑i,c i*∏e,v e^γ i e

def positivePart (c : Fin n→ℝ) (γ : Fin n→E→ℕ) (v : E→ℝ) : ℝ :=
  ∑i,(c i+|c i|+1)*∏e,v e^γ i e

def negativePart (c : Fin n→ℝ) (γ : Fin n→E→ℕ) (v : E→ℝ) : ℝ :=
  ∑i,(|c i|+1)*∏e,v e^γ i e

omit [DecidableEq E] in
theorem parts_difference (c : Fin n→ℝ) (γ : Fin n→E→ℕ) (v : E→ℝ) :
    positivePart c γ v-negativePart c γ v=polynomial c γ v := by
  unfold positivePart negativePart polynomial
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

def offsetBranch (K : ℝ) (hK : 0<K) (c : Fin n→ℝ) (hc : ∀i,0<c i)
    (γ : Fin n→E→ℕ) : Branch E n where
  coefficient := Fin.cases K c
  coefficient_pos := by intro i; refine Fin.cases hK (fun j=>hc j) i
  exponent := Fin.cases (fun _=>0) γ

def halfBranch (b : Branch E n) : Branch E n where
  coefficient := fun i=>b.coefficient i/2
  coefficient_pos := fun i=>div_pos (b.coefficient_pos i) (by norm_num)
  exponent := b.exponent

omit [DecidableEq E] in
theorem offset_resistance (K : ℝ) (hK : 0<K) (c : Fin n→ℝ) (hc : ∀i,0<c i)
    (γ : Fin n→E→ℕ) (u : E→ℝ) :
    (∑i,(offsetBranch K hK c hc γ).weight u i)=K+polynomial c γ (fun e=>(u e)⁻¹) := by
  rw [Fin.sum_univ_succ]
  simp only [Branch.weight,offsetBranch,Fin.cases_zero,Fin.cases_succ,pow_zero,
    Finset.prod_const_one,polynomial,inv_pow,Finset.prod_inv_distrib,div_eq_mul_inv,inv_one,mul_one]

omit [DecidableEq E] in
theorem half_resistance (b : Branch E n) (u : E→ℝ) :
    (∑i,(halfBranch b).weight u i)=(∑i,b.weight u i)/2 := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [Branch.weight,halfBranch]
  ring

def polynomialLeft (K : ℝ) (hK : 0<K) (c : Fin n→ℝ) (γ : Fin n→E→ℕ) : Branch E n :=
  offsetBranch K hK (fun i=>|c i|+1) (fun i=>by positivity) γ

def polynomialRight (K : ℝ) (hK : 0<K) (c : Fin n→ℝ) (γ : Fin n→E→ℕ) : Branch E n :=
  halfBranch (offsetBranch K hK (fun i=>c i+|c i|+1)
    (fun i=>by have h:=neg_abs_le (c i); linarith) γ)

theorem polynomial_source_iff (K : ℝ) (hK : 0<K) (c : Fin n→ℝ) (γ : Fin n→E→ℕ)
    (u : E→ℝ) (hu : ∀e,0<u e) :
    Compatible (polynomialLeft K hK c γ) (polynomialRight K hK c γ) u ↔
    0<polynomial c γ (fun e=>(u e)⁻¹) ∧
      positivePart c γ (fun e=>(u e)⁻¹)<3*K+4*negativePart c γ (fun e=>(u e)⁻¹) := by
  rw [compatible_iff_resistances _ _ u hu]
  unfold polynomialLeft polynomialRight
  rw [offset_resistance,half_resistance,offset_resistance]
  change (K+negativePart c γ _)<2*((K+positivePart c γ _)/2) ∧
    (K+positivePart c γ _)/2<2*(K+negativePart c γ _) ↔ _
  have hd:=parts_difference c γ (fun e=>(u e)⁻¹)
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem polynomial_source_large_offset (K : ℝ) (hK : 0<K) (c : Fin n→ℝ) (γ : Fin n→E→ℕ)
    (u : E→ℝ) (hu : ∀e,0<u e)
    (hbound : positivePart c γ (fun e=>(u e)⁻¹)<K) :
    Compatible (polynomialLeft K hK c γ) (polynomialRight K hK c γ) u ↔
      0<polynomial c γ (fun e=>(u e)⁻¹) := by
  rw [polynomial_source_iff K hK c γ u hu]
  have hn : 0≤negativePart c γ (fun e=>(u e)⁻¹) := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (by positivity)
    exact Finset.prod_nonneg (fun e _=>pow_nonneg (le_of_lt (inv_pos.mpr (hu e))) _)
  exact and_iff_left (by linarith)

omit [Fintype E] in
theorem polynomial_source_PACs (K : ℝ) (hK : 0<K) (c : Fin n→ℝ) (γ : Fin n→E→ℕ) :
    (leftCycle (polynomialLeft K hK c γ) (polynomialRight K hK c γ)).motif.IsPAC ∧
    (rightCycle (polynomialLeft K hK c γ) (polynomialRight K hK c γ)).motif.IsPAC :=
  supplied_cores_are_PACs _ _

end
end JointThermoComplexity.Emitted

#print axioms JointThermoComplexity.Emitted.polynomial_source_iff

#print axioms JointThermoComplexity.Emitted.polynomial_source_large_offset

#print axioms JointThermoComplexity.Emitted.polynomial_source_PACs
