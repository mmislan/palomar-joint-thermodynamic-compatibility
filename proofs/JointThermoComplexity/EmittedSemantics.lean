module
public import proofs.JointThermoComplexity.EmittedSource
public import proofs.JointThermoComplexity.CyclePathBridge
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity.Emitted
open ThermoCoreCompatibility ThermoCoreCompatibility.Hypergraph
open scoped BigOperators
noncomputable section

variable {E : Type*} [Fintype E] [DecidableEq E] {n m : ℕ}

omit [DecidableEq E] in
theorem padding_activity (z : Species E n m → ℝ) (γ : E → ℕ) :
    ReversibleCRN.complexActivity z (padding γ) = ∏ e,z (external e)^γ e := by
  simp [ReversibleCRN.complexActivity,Fintype.prod_sum_type,padding,external]

theorem left_current (L : Branch E n) (R : Branch E m) (z : Species E n m → ℝ) (i : Fin (n+2)) :
    (source L R).current z (.inl i) =
      (L.barrier i*(∏ e,z (external e)^L.powers i e))*
        (z (leftVertex i)-(z (leftVertex (finRotate (n+2) i)))^(cycleGain n i)) := by
  change L.barrier i*(ReversibleCRN.complexActivity z (fun s=>atom (leftVertex i) 1 s+padding (L.powers i) s)-
    ReversibleCRN.complexActivity z (fun s=>atom (leftVertex (finRotate (n+2) i)) (cycleGain n i) s+padding (L.powers i) s))=_
  rw [padded_current,padding_activity,activity_atom,activity_atom,pow_one]

theorem right_current (L : Branch E n) (R : Branch E m) (z : Species E n m → ℝ) (i : Fin (m+2)) :
    (source L R).current z (.inr i) =
      (R.barrier i*(∏ e,z (external e)^R.powers i e))*
        (z (rightVertex i)-(z (rightVertex (finRotate (m+2) i)))^(cycleGain m i)) := by
  change R.barrier i*(ReversibleCRN.complexActivity z (fun s=>atom (rightVertex i) 1 s+padding (R.powers i) s)-
    ReversibleCRN.complexActivity z (fun s=>atom (rightVertex (finRotate (m+2) i)) (cycleGain m i) s+padding (R.powers i) s))=_
  rw [padded_current,padding_activity,activity_atom,activity_atom,pow_one]

omit [DecidableEq E] in
theorem Branch.weight_pos (b : Branch E n) (u : E → ℝ) (hu : ∀e,0<u e) (i : Fin (n+1)) : 0<b.weight u i :=
  div_pos (b.coefficient_pos i) (Finset.prod_pos (fun e _=>pow_pos (hu e) _))

omit [DecidableEq E] in
theorem Branch.flux_formula (b : Branch E n) (u : E → ℝ) (hu : ∀e,0<u e)
    (p : Fin (n+2)→ℝ) (i : Fin (n+2)) :
    (b.barrier i*(∏e,u e^b.powers i e))*(p i-(p (finRotate (n+2) i))^(cycleGain n i)) =
      cycleFlux (b.weight u) p i := by
  by_cases hi : i.val=0
  · have he : i=0 := Fin.ext hi
    subst i
    have hlast : (0 : Fin (n+2)) ≠ Fin.last (n+1) := by intro h; have hh:=congrArg Fin.val h; simp at hh
    simp [Branch.barrier,Branch.powers,cycleFlux,cycleGain,hlast]
  · have hprod : (∏e,u e^b.exponent ⟨i.val-1,by omega⟩ e) ≠ 0 :=
      ne_of_gt (Finset.prod_pos (fun e _=>pow_pos (hu e) _))
    have hc := ne_of_gt (b.coefficient_pos ⟨i.val-1,by omega⟩)
    simp only [Branch.barrier,Branch.powers,cycleFlux,dite_eq_right hi,Branch.weight]
    field_simp

theorem left_flux (L : Branch E n) (R : Branch E m) (u : E→ℝ) (hu : ∀e,0<u e)
    (z : Species E n m→ℝ) (hz : ∀e,z (external e)=u e) (i : Fin (n+2)) :
    (source L R).current z (.inl i) = cycleFlux (L.weight u) (fun j=>z (leftVertex j)) i := by
  rw [left_current]
  simp_rw [hz]
  exact L.flux_formula u hu (fun j=>z (leftVertex j)) i

theorem right_flux (L : Branch E n) (R : Branch E m) (u : E→ℝ) (hu : ∀e,0<u e)
    (z : Species E n m→ℝ) (hz : ∀e,z (external e)=u e) (i : Fin (m+2)) :
    (source L R).current z (.inr i) = cycleFlux (R.weight u) (fun j=>z (rightVertex j)) i := by
  rw [right_current]
  simp_rw [hz]
  exact R.flux_formula u hu (fun j=>z (rightVertex j)) i

def assemble (u : E→ℝ) (p : Fin (n+2)→ℝ) (q : Fin (m+2)→ℝ) : Species E n m→ℝ :=
  fun s => match s with
    | .inl i => p i
    | .inr (.inl e) => u e
    | .inr (.inr j) => q ⟨j.val+2,by omega⟩

omit [Fintype E] [DecidableEq E] in
theorem assemble_right (u : E→ℝ) (p : Fin (n+2)→ℝ) (q : Fin (m+2)→ℝ)
    (h0 : p 0=q 0) (h1 : p 1=q 1) (i : Fin (m+2)) :
    assemble u p q (rightVertex i)=q i := by
  unfold rightVertex
  split_ifs with hi0 hi1
  · have he : i=0 := Fin.ext hi0
    subst i
    exact h0
  · have he : i=1 := by apply Fin.ext; simpa using hi1
    subst i
    exact h1
  · change q ⟨i.val-2+2,_⟩=q i
    congr 1
    apply Fin.ext
    dsimp
    omega

end
end JointThermoComplexity.Emitted

#print axioms JointThermoComplexity.Emitted.left_flux

#print axioms JointThermoComplexity.Emitted.right_flux

#print axioms JointThermoComplexity.Emitted.assemble_right
