module
public import proofs.JointThermoComplexity.BoxedReduction

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity.Emitted
open scoped BigOperators
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}

def variableOffsetBranch (c : Fin n→ℝ) (hc : ∀i,0<c i) (γ : Fin n→E→ℕ) : Branch (Option E) n where
  coefficient := Fin.cases 1 c
  coefficient_pos := by intro i; exact Fin.cases (by norm_num) hc i
  exponent := Fin.cases (fun e=>match e with | none=>1 | some _=>0)
    (fun i e=>match e with | none=>0 | some e=>γ i e)

omit [DecidableEq E] in
theorem variable_resistance (c : Fin n→ℝ) (hc : ∀i,0<c i) (γ : Fin n→E→ℕ) (u : Option E→ℝ) :
    (∑i,(variableOffsetBranch c hc γ).weight u i)=
      (u none)⁻¹+polynomial c γ (fun e=>(u (some e))⁻¹) := by
  rw [Fin.sum_univ_succ]
  simp [Branch.weight,variableOffsetBranch,Fintype.prod_option,polynomial,
    inv_pow,Finset.prod_inv_distrib,div_eq_mul_inv]

def unboxedLeft (c : Fin n→ℝ) (γ : Fin n→E→ℕ) : Branch (Option E) n :=
  variableOffsetBranch (fun i=>|c i|+1) (fun i=>by positivity) γ

def unboxedRight (c : Fin n→ℝ) (γ : Fin n→E→ℕ) : Branch (Option E) n :=
  halfBranch (variableOffsetBranch (fun i=>c i+|c i|+1)
    (fun i=>by have h:=neg_abs_le (c i); linarith) γ)

theorem unboxed_pointwise (c : Fin n→ℝ) (γ : Fin n→E→ℕ)
    (u : Option E→ℝ) (hu : ∀e,0<u e) :
    Compatible (unboxedLeft c γ) (unboxedRight c γ) u ↔
    0<polynomial c γ (fun e=>(u (some e))⁻¹) ∧
    positivePart c γ (fun e=>(u (some e))⁻¹)<
      3*(u none)⁻¹+4*negativePart c γ (fun e=>(u (some e))⁻¹) := by
  rw [compatible_iff_resistances _ _ u hu]
  unfold unboxedLeft unboxedRight
  rw [variable_resistance,half_resistance,variable_resistance]
  change (u none)⁻¹+negativePart c γ _<2*(((u none)⁻¹+positivePart c γ _)/2) ∧
    ((u none)⁻¹+positivePart c γ _)/2<2*((u none)⁻¹+negativePart c γ _) ↔ _
  have hd:=parts_difference c γ (fun e=>(u (some e))⁻¹)
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem unboxed_reduction (c : Fin n→ℝ) (γ : Fin n→E→ℕ) :
    (leftCycle (unboxedLeft c γ) (unboxedRight c γ)).motif.IsPAC ∧
    (rightCycle (unboxedLeft c γ) (unboxedRight c γ)).motif.IsPAC ∧
    ((∃v : E→ℝ,(∀e,0<v e) ∧ 0<polynomial c γ v) ↔
      (∃u : Option E→ℝ,(∀e,0<u e) ∧ Compatible (unboxedLeft c γ) (unboxedRight c γ) u)) := by
  refine ⟨(supplied_cores_are_PACs _ _).1,(supplied_cores_are_PACs _ _).2,?_⟩
  constructor
  · rintro ⟨v,hv,hp⟩
    let K:=1+|positivePart c γ v|
    have hK:0<K := by dsimp [K]; positivity
    let u : Option E→ℝ:=fun e=>match e with | none=>K⁻¹ | some e=>(v e)⁻¹
    have hu : ∀e,0<u e := by intro e; cases e with
      | none => exact inv_pos.mpr hK
      | some e => exact inv_pos.mpr (hv e)
    refine ⟨u,hu,(unboxed_pointwise c γ u hu).mpr ?_⟩
    simp only [u,inv_inv]
    have hn : 0≤negativePart c γ v := by
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun e _=>pow_nonneg (le_of_lt (hv e)) _))
    have hq : positivePart c γ v<K := by dsimp [K]; linarith [le_abs_self (positivePart c γ v)]
    exact ⟨hp,by linarith⟩
  · rintro ⟨u,hu,hc⟩
    exact ⟨fun e=>(u (some e))⁻¹,fun e=>inv_pos.mpr (hu (some e)),
      ((unboxed_pointwise c γ u hu).mp hc).1⟩

end
end JointThermoComplexity.Emitted

#print axioms JointThermoComplexity.Emitted.unboxed_reduction

#print axioms JointThermoComplexity.Emitted.unboxed_reduction
