module
public import proofs.JointThermoComplexity.BoxedSource

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity.Emitted
open scoped BigOperators
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}

/-- The entire normalized sparse-polynomial reduction, including both promised
signed PACs and both directions for one literal globally shared source state. -/
theorem boxed_reduction (c : Fin n→ℝ) (γ : Fin n→E→ℕ) :
    let L:=polynomialLeft (offsetBound c γ) (offsetBound_pos c γ) c γ
    let R:=polynomialRight (offsetBound c γ) (offsetBound_pos c γ) c γ
    (leftCycle L R).motif.IsPAC ∧ (rightCycle L R).motif.IsPAC ∧
    ((∃v : E→ℝ,(∀e,1≤v e ∧ v e≤2) ∧ 0<polynomial c γ v) ↔
     (∃u : E→ℝ,(∀e,1/2≤u e ∧ u e≤1) ∧ BoxCompatible L R u)) := by
  dsimp only
  refine ⟨(supplied_cores_are_PACs _ _).1,(supplied_cores_are_PACs _ _).2,?_⟩
  constructor
  · rintro ⟨v,hv,hp⟩
    have hpos : ∀e,0<v e := fun e=>by linarith [(hv e).1]
    have hb : ∀e,1/2≤(v e)⁻¹ ∧ (v e)⁻¹≤1 := by
      intro e
      constructor
      · rw [← one_div,le_div_iff₀ (hpos e)]
        linarith [(hv e).2]
      · rw [inv_le_iff_one_le_mul₀ (hpos e)]
        linarith [(hv e).1]
    refine ⟨fun e=>(v e)⁻¹,hb,?_⟩
    apply (boxed_polynomial_source_iff c γ _ (fun e=>(hb e).1)).mpr
    simpa only [inv_inv] using hp
  · rintro ⟨u,hu,hc⟩
    have hpos : ∀e,0<u e := fun e=>by linarith [(hu e).1]
    refine ⟨fun e=>(u e)⁻¹,?_,(boxed_polynomial_source_iff c γ u (fun e=>(hu e).1)).mp hc⟩
    intro e
    change 1≤(u e)⁻¹ ∧ (u e)⁻¹≤2
    constructor
    · rw [← one_div,le_div_iff₀ (hpos e)]
      linarith [(hu e).2]
    · rw [inv_le_iff_one_le_mul₀ (hpos e)]
      linarith [(hu e).1]

theorem emitted_reference_equilibrium (L : Branch E n) {m : ℕ} (R : Branch E m) :
    ∀r,(source L R).current (fun _=>1) r=0 := by
  intro r
  simp [ThermoCoreCompatibility.ReversibleCRN.current,
    ThermoCoreCompatibility.ReversibleCRN.complexActivity]

end
end JointThermoComplexity.Emitted

#print axioms JointThermoComplexity.Emitted.boxed_reduction
#print axioms JointThermoComplexity.Emitted.emitted_reference_equilibrium

#print axioms JointThermoComplexity.Emitted.boxed_reduction

#print axioms JointThermoComplexity.Emitted.emitted_reference_equilibrium
