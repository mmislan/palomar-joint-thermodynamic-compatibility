module
public import proofs.JointThermoComplexity.PolynomialSource

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity.Emitted
open scoped BigOperators
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E] {n m : ℕ}

def BoxCompatible (L : Branch E n) (R : Branch E m) (u : E→ℝ) : Prop :=
  ∃ z : Species E n m→ℝ, (∀s,0<z s) ∧ (∀e,z (external e)=u e) ∧
    (∀r,0<(source L R).current z r) ∧
    (leftCycle L R).motif.Productive ((source L R).current z) ∧
    (rightCycle L R).motif.Productive ((source L R).current z) ∧
    (∀i,1/4≤z (leftVertex i) ∧ z (leftVertex i)≤1/2) ∧
    (∀i,1/4≤z (rightVertex i) ∧ z (rightVertex i)≤1/2)

omit [Fintype E] [DecidableEq E] in
theorem values_box {k : ℕ} (x : ℕ→ℝ) (hx : ∀i≤k+1,1/4≤x i ∧ x i<1/2)
    (i : Fin (k+2)) : 1/4≤cycleValues (1/2) x i ∧ cycleValues (1/2) x i≤1/2 := by
  unfold cycleValues
  split_ifs
  · norm_num
  · exact ⟨(hx _ (by omega)).1,le_of_lt (hx _ (by omega)).2⟩

theorem boxed_iff_compatible (L : Branch E n) (R : Branch E m)
    (u : E→ℝ) (hu : ∀e,0<u e) : BoxCompatible L R u ↔ Compatible L R u := by
  constructor
  · rintro ⟨z,hz,he,hj,hL,hR,_,_⟩
    exact ⟨z,hz,he,hj,hL,hR⟩
  · intro hc
    obtain ⟨h₁,h₂⟩:=(compatible_iff_resistances L R u hu).mp hc
    have hw:=L.weight_pos u hu
    have hv:=R.weight_pos u hu
    have hwR:0<∑i,L.weight u i := Finset.sum_pos (fun i _=>hw i) ⟨0,Finset.mem_univ _⟩
    have hvR:0<∑i,R.weight u i := Finset.sum_pos (fun i _=>hv i) ⟨0,Finset.mem_univ _⟩
    obtain ⟨t,ht₁,ht₂,ht₃,ht₄⟩:=(intervals_overlap_iff _ _).mpr ⟨hwR,hvR,h₁,h₂⟩
    obtain ⟨x,hx,hxb⟩:=literal_path_construct (by omega) (L.weight u) hw t ht₁ ht₂
    obtain ⟨y,hy,hyb⟩:=literal_path_construct (by omega) (R.weight u) hv t ht₃ ht₄
    obtain ⟨hp,ha,hg⟩:=path_to_productive_cycle (L.weight u) (1/2) _ x (by norm_num) hx
    obtain ⟨hq,hb,hh⟩:=path_to_productive_cycle (R.weight u) (1/2) _ y (by norm_num) hy
    let p : Fin (n+2)→ℝ:=cycleValues (1/2) x
    let q : Fin (m+2)→ℝ:=cycleValues (1/2) y
    have h0 : p 0=q 0 := by simp [p,q,cycleValues]
    have h1 : p 1=q 1 := by simpa [p,q,cycleValues] using hx.1.trans hy.1.symm
    let z:=assemble u p q
    have he : ∀e,z (external e)=u e := fun _=>rfl
    have hl (i) : (source L R).current z (.inl i)=cycleFlux (L.weight u) p i :=
      left_flux L R u hu z he i
    have hr (i) : (source L R).current z (.inr i)=cycleFlux (R.weight u) q i := by
      rw [right_flux L R u hu z he]
      have hv' : (fun j=>z (rightVertex j))=q := funext (assemble_right u p q h0 h1)
      rw [hv']
    refine ⟨z,?_,he,?_,?_,?_,?_,?_⟩
    · intro s
      cases s with
      | inl i => exact hp i
      | inr s => cases s with
        | inl e => exact hu e
        | inr i => exact hq _
    · intro r
      cases r with
      | inl i => rw [hl]; exact chain_positive _ ha hg i
      | inr i => rw [hr]; exact chain_positive _ hb hh i
    · apply (leftCycle L R).productive_iff_chain _ |>.mpr
      dsimp only [leftCycle]
      simp_rw [hl]
      exact ⟨ha,hg⟩
    · apply (rightCycle L R).productive_iff_chain _ |>.mpr
      dsimp only [rightCycle]
      simp_rw [hr]
      exact ⟨hb,hh⟩
    · intro i
      exact values_box x hxb i
    · intro i
      change 1/4≤assemble u p q (rightVertex i) ∧ assemble u p q (rightVertex i)≤1/2
      rw [assemble_right u p q h0 h1]
      exact values_box y hyb i

def offsetBound {k : ℕ} (c : Fin k→ℝ) (γ : Fin k→E→ℕ) : ℝ :=
  1+∑i,(c i+|c i|+1)*∏e,(2:ℝ)^γ i e

omit [DecidableEq E] in
theorem offsetBound_pos {k : ℕ} (c : Fin k→ℝ) (γ : Fin k→E→ℕ) : 0<offsetBound c γ := by
  have h : 0≤∑i,(c i+|c i|+1)*∏e,(2:ℝ)^γ i e := by
    apply Finset.sum_nonneg
    intro i _
    have hc:=neg_abs_le (c i)
    apply mul_nonneg (by linarith)
    exact Finset.prod_nonneg (fun _ _=>by positivity)
  unfold offsetBound
  linarith

omit [DecidableEq E] in
theorem positivePart_bound {k : ℕ} (c : Fin k→ℝ) (γ : Fin k→E→ℕ)
    (u : E→ℝ) (hu : ∀e,1/2≤u e) : positivePart c γ (fun e=>(u e)⁻¹)<offsetBound c γ := by
  have h : positivePart c γ (fun e=>(u e)⁻¹)≤offsetBound c γ-1 := by
    unfold positivePart offsetBound
    simp only [add_sub_cancel_left]
    apply Finset.sum_le_sum
    intro i _
    have hc:=neg_abs_le (c i)
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Finset.prod_le_prod₀
    · intro e _
      exact pow_nonneg (le_of_lt (inv_pos.mpr (by linarith [hu e]))) _
    · intro e _
      apply pow_le_pow_left₀ (le_of_lt (inv_pos.mpr (by linarith [hu e])))
      rw [inv_le_iff_one_le_mul₀ (by linarith [hu e])]
      linarith [hu e]
  linarith

theorem boxed_polynomial_source_iff {k : ℕ} (c : Fin k→ℝ) (γ : Fin k→E→ℕ)
    (u : E→ℝ) (hu : ∀e,1/2≤u e) :
    BoxCompatible (polynomialLeft (offsetBound c γ) (offsetBound_pos c γ) c γ)
      (polynomialRight (offsetBound c γ) (offsetBound_pos c γ) c γ) u ↔
    0<polynomial c γ (fun e=>(u e)⁻¹) := by
  have hp : ∀e,0<u e := fun e=>by linarith [hu e]
  rw [boxed_iff_compatible _ _ u hp]
  exact polynomial_source_large_offset _ (offsetBound_pos c γ) c γ u hp (positivePart_bound c γ u hu)

end
end JointThermoComplexity.Emitted

#print axioms JointThermoComplexity.Emitted.boxed_iff_compatible

#print axioms JointThermoComplexity.Emitted.boxed_polynomial_source_iff
