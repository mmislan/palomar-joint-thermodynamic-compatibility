module
public import proofs.JointThermoComplexity.Complexity.RationalBranchData
public import proofs.JointThermoComplexity.FamilyDock

set_option autoImplicit false
@[expose] public section

/-! Executable external-coordinate relabeling preserves resistance comparisons
and common-state compatibility. No independent state is introduced per core. -/

namespace JointThermoComplexity.Complexity.RationalBranchRelabel
open RationalBranchData
open scoped BigOperators
variable {E F : Type} {n m : ℕ}

def relabel (e : E ≃ F) (b : Data E n) : Data F n where
  numerator := b.numerator
  denominator := b.denominator
  numerator_pos := b.numerator_pos
  denominator_pos := b.denominator_pos
  exponent i f := b.exponent i (e.symm f)

theorem weight_relabel [Fintype E] [Fintype F] (e : E ≃ F) (b : Data E n)
    (u : F → ℝ) (i : Fin (n + 1)) :
    (relabel e b).toBranch.weight u i = b.toBranch.weight (u ∘ e) i := by
  have hp : (∏ f, u f ^ b.exponent i (e.symm f)) = ∏ a, u (e a) ^ b.exponent i a := by
    simpa only [Equiv.symm_apply_apply] using
      (e.prod_comp (fun f => u f ^ b.exponent i (e.symm f))).symm
  simp only [Emitted.Branch.weight, Data.toBranch, relabel, Function.comp_apply]
  rw [hp]

theorem compatible_relabel [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (e : E ≃ F) (L : Data E n) (R : Data E m) (u : F → ℝ) (hu : ∀ f, 0 < u f) :
    Emitted.Compatible (relabel e L).toBranch (relabel e R).toBranch u ↔
      Emitted.Compatible L.toBranch R.toBranch (u ∘ e) := by
  rw [Emitted.compatible_iff_resistances _ _ u hu,
    Emitted.compatible_iff_resistances _ _ (u ∘ e) (fun a => hu (e a))]
  simp only [weight_relabel]

theorem multicac_relabel [Fintype E] [Fintype F] [DecidableEq E] [DecidableEq F]
    (e : E ≃ F) (L : Data E n) (R : Data E m) :
    (Emitted.family (relabel e L).toBranch (relabel e R).toBranch).MultiCAC ↔
      (Emitted.family L.toBranch R.toBranch).MultiCAC := by
  rw [Emitted.family_multicac_iff, Emitted.family_multicac_iff]
  constructor
  · rintro ⟨u, hu, hc⟩
    exact ⟨u ∘ e, (fun a => hu (e a)), (compatible_relabel e L R u hu).mp hc⟩
  · rintro ⟨u, hu, hc⟩
    let v : F → ℝ := u ∘ e.symm
    have hv : ∀ f, 0 < v f := fun f => hu (e.symm f)
    refine ⟨v, hv, (compatible_relabel e L R v hv).mpr ?_⟩
    have he : v ∘ e = u := by funext a; simp only [v, Function.comp_apply, Equiv.symm_apply_apply]
    rw [he]
    exact hc

end JointThermoComplexity.Complexity.RationalBranchRelabel

#print axioms JointThermoComplexity.Complexity.RationalBranchRelabel.relabel
#print axioms JointThermoComplexity.Complexity.RationalBranchRelabel.weight_relabel
#print axioms JointThermoComplexity.Complexity.RationalBranchRelabel.compatible_relabel
#print axioms JointThermoComplexity.Complexity.RationalBranchRelabel.multicac_relabel
