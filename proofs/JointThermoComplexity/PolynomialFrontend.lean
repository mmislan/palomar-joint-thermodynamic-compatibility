module
public import proofs.JointThermoComplexity.OpenCubeReduction
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity.Emitted
open scoped BigOperators
open MvPolynomial
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E]

def termIndex (p : MvPolynomial E ℝ) : Fin (Fintype.card p.support) ≃ p.support :=
  (Fintype.equivFin p.support).symm

def coefficients (p : MvPolynomial E ℝ) (i : Fin (Fintype.card p.support)) : ℝ :=
  p.coeff (termIndex p i).val

def exponents (p : MvPolynomial E ℝ) (i : Fin (Fintype.card p.support)) (e : E) : ℕ :=
  (termIndex p i).val e

omit [DecidableEq E] in
theorem sparse_eval (p : MvPolynomial E ℝ) (v : E→ℝ) :
    polynomial (coefficients p) (exponents p) v=eval v p := by
  unfold polynomial coefficients exponents
  rw [(termIndex p).sum_comp (fun d : p.support=>p.coeff d.val*∏e,v e^d.val e)]
  rw [MvPolynomial.eval_eq']
  exact Finset.sum_coe_sort p.support (fun d=>p.coeff d*∏e,v e^d e)

def cubePolynomial (p : MvPolynomial E ℝ) : MvPolynomial E ℝ :=
  eval₂Hom C (fun e=>C 2*X e-C 3) p

omit [Fintype E] [DecidableEq E] in
theorem cubePolynomial_eval (p : MvPolynomial E ℝ) (v : E→ℝ) :
    eval v (cubePolynomial p)=eval (fun e=>2*v e-3) p := by
  unfold cubePolynomial
  rw [map_eval₂Hom]
  congr 1
  ext r <;> simp [eval₂Hom_X']

def orthantPolynomial (p : MvPolynomial E ℝ) : MvPolynomial (E ⊕ E) ℝ :=
  eval₂Hom C (fun e=>X (.inl e)-X (.inr e)) p

omit [Fintype E] [DecidableEq E] in
theorem orthantPolynomial_eval (p : MvPolynomial E ℝ) (v : E ⊕ E→ℝ) :
    eval v (orthantPolynomial p)=eval (fun e=>v (.inl e)-v (.inr e)) p := by
  unfold orthantPolynomial
  rw [map_eval₂Hom]
  congr 1
  ext r <;> simp [eval₂Hom_X']

omit [DecidableEq E] in
theorem cube_frontend (p : MvPolynomial E ℝ) :
    (∃x : E→ℝ,(∀e,-1<x e ∧ x e<1) ∧ 0<eval x p) ↔
    (∃v : E→ℝ,(∀e,1<v e ∧ v e<2) ∧
      0<polynomial (coefficients (cubePolynomial p)) (exponents (cubePolynomial p)) v) := by
  simp only [sparse_eval,cubePolynomial_eval]
  constructor
  · rintro ⟨x,hx,hp⟩
    refine ⟨fun e=>(x e+3)/2,fun e=>⟨by linarith [(hx e).1],by linarith [(hx e).2]⟩,?_⟩
    have he : (fun e=>2*((x e+3)/2)-3)=x := by funext e; ring
    simpa only [he] using hp
  · rintro ⟨v,hv,hp⟩
    exact ⟨fun e=>2*v e-3,fun e=>⟨by linarith [(hv e).1],by linarith [(hv e).2]⟩,hp⟩

omit [DecidableEq E] in
theorem orthant_frontend (p : MvPolynomial E ℝ) :
    (∃x : E→ℝ,0<eval x p) ↔
    (∃v : E ⊕ E→ℝ,(∀e,0<v e) ∧
      0<polynomial (coefficients (orthantPolynomial p)) (exponents (orthantPolynomial p)) v) := by
  simp only [sparse_eval,orthantPolynomial_eval]
  constructor
  · rintro ⟨x,hp⟩
    let v : E ⊕ E→ℝ:=Sum.elim (fun e=>x e+|x e|+1) (fun e=>|x e|+1)
    refine ⟨v,?_,?_⟩
    · intro e
      cases e with
      | inl e => have h:=neg_abs_le (x e); dsimp [v]; linarith
      | inr e => dsimp [v]; positivity
    · have he : (fun e=>v (.inl e)-v (.inr e))=x := by funext e; dsimp [v]; ring
      simpa only [he] using hp
  · rintro ⟨v,_,hp⟩
    exact ⟨_,hp⟩

theorem full_boxed_reduction (p : MvPolynomial E ℝ) :
    let g:=cubePolynomial p
    let c:=coefficients g
    let γ:=exponents g
    let L:=polynomialLeft (offsetBound c γ) (offsetBound_pos c γ) c γ
    let R:=polynomialRight (offsetBound c γ) (offsetBound_pos c γ) c γ
    (leftCycle L R).motif.IsPAC ∧ (rightCycle L R).motif.IsPAC ∧
    ((∃x : E→ℝ,(∀e,-1<x e ∧ x e<1) ∧ 0<eval x p) ↔
     (∃u : E→ℝ,(∀e,1/2≤u e ∧ u e≤1) ∧ BoxCompatible L R u)) := by
  have h:=boxed_open_reduction (coefficients (cubePolynomial p)) (exponents (cubePolynomial p))
  exact ⟨h.1,h.2.1,(cube_frontend p).trans h.2.2⟩

theorem full_unboxed_reduction (p : MvPolynomial E ℝ) :
    (family (unboxedLeft (coefficients (orthantPolynomial p)) (exponents (orthantPolynomial p)))
      (unboxedRight (coefficients (orthantPolynomial p)) (exponents (orthantPolynomial p)))).MultiCAC ↔
      ∃x : E→ℝ,0<eval x p := by
  rw [source_unboxed_reduction]
  exact (orthant_frontend p).symm

end
end JointThermoComplexity.Emitted

#print axioms JointThermoComplexity.Emitted.full_boxed_reduction
#print axioms JointThermoComplexity.Emitted.full_unboxed_reduction

#print axioms JointThermoComplexity.Emitted.full_boxed_reduction

#print axioms JointThermoComplexity.Emitted.full_unboxed_reduction
