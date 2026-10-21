module
public import proofs.JointThermoComplexity.UnboxedReduction
public import proofs.ThermoCoreCompatibility.CoreFamily

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity.Emitted
open ThermoCoreCompatibility
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E] {n m : ℕ}

def family (L : Branch E n) (R : Branch E m) : CoreFamily (Core:=Bool) (source L R) where
  core := fun b=>if b then (rightCycle L R).motif else (leftCycle L R).motif
  core_isPAC := by
    intro b
    cases b
    · exact (leftCycle L R).isPAC
    · exact (rightCycle L R).isPAC
  orientation := fun _=>1
  orientation_unit := fun _=>Or.inl rfl
  owner := Sum.elim (fun _=>false) (fun _=>true)
  owner_mem := by
    intro r
    cases r with
    | inl i => simp [CycleIn.motif,leftCycle]
    | inr i => simp [CycleIn.motif,rightCycle]

theorem family_multicac_iff (L : Branch E n) (R : Branch E m) :
    (family L R).MultiCAC ↔ ∃u : E→ℝ,(∀e,0<u e) ∧ Compatible L R u := by
  constructor
  · rintro ⟨z,hz,hj,hp⟩
    refine ⟨fun e=>z (external e),fun e=>hz _,z,hz,fun _=>rfl,?_,?_,?_⟩
    · simpa only [family,Int.cast_one,one_mul] using hj
    · simpa only [family,Bool.false_eq_true,↓reduceIte] using hp false
    · simpa only [family,↓reduceIte] using hp true
  · rintro ⟨_,_,z,hz,_,hj,hL,hR⟩
    refine ⟨z,hz,?_,?_⟩
    · simpa only [family,Int.cast_one,one_mul] using hj
    · intro b
      cases b
      · exact hL
      · exact hR

theorem source_unboxed_reduction (c : Fin n→ℝ) (γ : Fin n→E→ℕ) :
    (family (unboxedLeft c γ) (unboxedRight c γ)).MultiCAC ↔
      ∃v : E→ℝ,(∀e,0<v e) ∧ 0<polynomial c γ v := by
  rw [family_multicac_iff]
  exact (unboxed_reduction c γ).2.2.symm

end
end JointThermoComplexity.Emitted

#print axioms JointThermoComplexity.Emitted.source_unboxed_reduction
#print axioms JointThermoComplexity.Emitted.boxed_reduction

#print axioms JointThermoComplexity.Emitted.source_unboxed_reduction
