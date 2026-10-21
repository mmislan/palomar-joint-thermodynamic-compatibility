module
public import proofs.JointThermoComplexity.FamilyDock
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Tactic.FunProp

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity.Emitted
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}

omit [DecidableEq E] in
theorem polynomial_continuous (c : Fin n→ℝ) (γ : Fin n→E→ℕ) : Continuous (polynomial c γ) := by
  unfold polynomial
  fun_prop

omit [Fintype E] [DecidableEq E] in
theorem open_closed_cube (f : (E→ℝ)→ℝ) (hf : Continuous f) :
    (∃v : E→ℝ,(∀e,1<v e ∧ v e<2) ∧ 0<f v) ↔
    (∃v : E→ℝ,(∀e,1≤v e ∧ v e≤2) ∧ 0<f v) := by
  constructor
  · rintro ⟨v,hv,hp⟩
    exact ⟨v,fun e=>⟨le_of_lt (hv e).1,le_of_lt (hv e).2⟩,hp⟩
  · rintro ⟨v,hv,hp⟩
    let s : Set (E→ℝ):=Set.pi Set.univ (fun _=>Set.Ioo (1:ℝ) 2)
    have hc : v∈closure s := by
      dsimp [s]
      rw [closure_pi_set]
      simp only [closure_Ioo (by norm_num : (1:ℝ)≠2),Set.mem_pi,Set.mem_univ,true_implies,Set.mem_Icc]
      exact hv
    have ho : IsOpen {x | 0<f x} := isOpen_lt continuous_const hf
    obtain ⟨x,hxp,hxs⟩:=mem_closure_iff.mp hc _ ho hp
    exact ⟨x,fun e=>hxs e (Set.mem_univ e),hxp⟩

theorem boxed_open_reduction (c : Fin n→ℝ) (γ : Fin n→E→ℕ) :
    let L:=polynomialLeft (offsetBound c γ) (offsetBound_pos c γ) c γ
    let R:=polynomialRight (offsetBound c γ) (offsetBound_pos c γ) c γ
    (leftCycle L R).motif.IsPAC ∧ (rightCycle L R).motif.IsPAC ∧
    ((∃v : E→ℝ,(∀e,1<v e ∧ v e<2) ∧ 0<polynomial c γ v) ↔
     (∃u : E→ℝ,(∀e,1/2≤u e ∧ u e≤1) ∧ BoxCompatible L R u)) := by
  have h:=boxed_reduction c γ
  refine ⟨h.1,h.2.1,?_⟩
  exact (open_closed_cube _ (polynomial_continuous c γ)).trans h.2.2

end
end JointThermoComplexity.Emitted

#print axioms JointThermoComplexity.Emitted.boxed_open_reduction
#print axioms JointThermoComplexity.Emitted.source_unboxed_reduction

#print axioms JointThermoComplexity.Emitted.boxed_open_reduction
