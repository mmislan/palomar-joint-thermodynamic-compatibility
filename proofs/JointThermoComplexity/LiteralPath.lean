module
public import proofs.JointThermoComplexity.PathReconstruction
public import proofs.JointThermoComplexity.ResistanceComparator
public import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity
open scoped BigOperators

noncomputable def extendFin {n : ℕ} (f : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i<n then f ⟨i,h⟩ else 0

theorem extendFin_at {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : extendFin f i.val=f i := by
  simp [extendFin, i.isLt]

theorem sum_extendFin {n : ℕ} (f : Fin n → ℝ) :
    (∑ i ∈ Finset.range n, extendFin f i) = ∑ i, f i := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [extendFin_at]

/-- Literal private-edge currents; no independent complex variables are introduced. -/
noncomputable def pathCurrent {n : ℕ} (w : Fin n → ℝ) (x : ℕ → ℝ) (i : Fin n) : ℝ :=
  (x i.val-x (i.val+1))/w i

def LiteralPath {n : ℕ} (w : Fin n → ℝ) (A B : ℝ) (x : ℕ → ℝ) : Prop :=
  x 0=B ∧ x n=A^2 ∧ (∀ k≤n, 0<x k) ∧
  0<A-B ∧ (∀ i, (A-B)/2<pathCurrent w x i ∧ pathCurrent w x i<A-B) ∧
  StrictAnti (pathCurrent w x)

theorem path_telescope {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i,0<w i) (x : ℕ → ℝ) :
    (∑ i, w i*pathCurrent w x i)=x 0-x n := by
  have hterm (i : Fin n) : w i*pathCurrent w x i=x i.val-x (i.val+1) := by
    dsimp [pathCurrent]
    field_simp [ne_of_gt (hw i)]
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun i => x i-x (i+1))]
  exact Finset.sum_range_sub' x n

theorem literal_path_necessary {n : ℕ} (hn : 0<n) (w : Fin n → ℝ)
    (hw : ∀ i,0<w i) (A B : ℝ) (x : ℕ → ℝ) (h : LiteralPath w A B x) :
    (∑ i,w i)/2 < (B-A^2)/(A-B) ∧ (B-A^2)/(A-B)<∑ i,w i := by
  obtain ⟨h0,hnx,_,hj,ht,_⟩ := h
  let t : Fin n → ℝ := fun i => pathCurrent w x i/(A-B)
  have hb (i) : 1/2<t i ∧ t i<1 := by
    constructor
    · exact (lt_div_iff₀ hj).2 (by linarith [(ht i).1])
    · exact (div_lt_iff₀ hj).2 (by simpa using (ht i).2)
  have he : (∑ i,w i*t i)=(B-A^2)/(A-B) := by
    dsimp [t]
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, path_telescope w hw, h0, hnx]
  rw [← he]
  exact weighted_chain_necessary hn w t hw hb

/-- Completeness reconstructs actual positive species activities in fixed boxes. -/
theorem literal_path_construct {n : ℕ} (hn : 0<n) (w : Fin n → ℝ)
    (hw : ∀ i,0<w i) (q : ℝ)
    (hlo : (∑ i,w i)/2<q) (hhi : q<∑ i,w i) :
    ∃ x : ℕ → ℝ,
      LiteralPath w (1/2) ((1/4+q/2)/(1+q)) x ∧
      (∀ k≤n, 1/4≤x k ∧ x k<1/2) := by
  have hR : 0<∑ i,w i := Finset.sum_pos (fun i _=>hw i) ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  have hq : 0<q := by linarith
  obtain ⟨t,ht,hdesc,hsum⟩ := weighted_chain_exists n hn w hw q hlo hhi
  have hw' (i) (hi:i<n) : 0<extendFin w i := by simpa [extendFin,hi] using hw ⟨i,hi⟩
  have ht' (i) (hi:i<n) : 1/2<extendFin t i ∧ extendFin t i<1 := by simpa [extendFin,hi] using ht ⟨i,hi⟩
  have hsum' : (∑ i∈Finset.range n,extendFin w i*extendFin t i)=q := by
    rw [← Fin.sum_univ_eq_sum_range]
    simpa only [extendFin_at] using hsum
  obtain ⟨B,j,x,hB,hj,hjpos,h0,hend,hbox,hcurr⟩ :=
    reconstruct_path n (extendFin w) (extendFin t) q hq hw' ht' hsum'
  have htel := path_telescope w hw x
  have he (i:Fin n) : pathCurrent w x i=j*t i := by
    have hh:=hcurr i.val i.isLt
    simpa only [extendFin_at,pathCurrent] using hh
  have hdrop : B-1/4=j*q := by
    simp_rw [he] at htel
    have heq : (∑ i,w i*(j*t i))=j*q := by
      calc
        _ = j*(∑ i,w i*t i) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
        _ = _ := by rw [hsum]
    rw [heq,h0,hend] at htel
    linarith
  have hBexact : B=(1/4+q/2)/(1+q) := by
    apply (eq_div_iff (by positivity : (1+q:ℝ) ≠ 0)).2
    rw [hj] at hdrop
    nlinarith
  refine ⟨x,?_,hbox⟩
  rw [← hBexact]
  refine ⟨h0,by norm_num; exact hend,fun k hk=>by linarith [(hbox k hk).1],?_,?_,?_⟩
  · simpa only [hj] using hjpos
  · intro i
    rw [he,← hj]
    have hl:=mul_lt_mul_of_pos_left (ht i).1 hjpos
    have hh:=mul_lt_mul_of_pos_left (ht i).2 hjpos
    constructor <;> nlinarith
  · intro i k hik
    rw [he,he]
    exact mul_lt_mul_of_pos_left (hdesc i k hik) hjpos

theorem literal_two_path_iff {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (w : Fin n → ℝ) (v : Fin m → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) :
    (∃ A B : ℝ, ∃ x y : ℕ→ℝ, 0<A ∧ LiteralPath w A B x ∧ LiteralPath v A B y) ↔
      (∑ i,w i)<2*(∑ i,v i) ∧ (∑ i,v i)<2*(∑ i,w i) := by
  constructor
  · rintro ⟨A,B,x,y,_,hx,hy⟩
    have h₁:=literal_path_necessary hn w hw A B x hx
    have h₂:=literal_path_necessary hm v hv A B y hy
    constructor <;> linarith
  · rintro ⟨h₁,h₂⟩
    have hwR:0<∑i,w i := Finset.sum_pos (fun i _=>hw i) ⟨⟨0,hn⟩,Finset.mem_univ _⟩
    have hvR:0<∑i,v i := Finset.sum_pos (fun i _=>hv i) ⟨⟨0,hm⟩,Finset.mem_univ _⟩
    obtain ⟨q,hq₁,hq₂,hq₃,hq₄⟩ := (intervals_overlap_iff _ _).2 ⟨hwR,hvR,h₁,h₂⟩
    obtain ⟨x,hx,_⟩ := literal_path_construct hn w hw q hq₁ hq₂
    obtain ⟨y,hy,_⟩ := literal_path_construct hm v hv q hq₃ hq₄
    exact ⟨1/2,_,x,y,by norm_num,hx,hy⟩

end JointThermoComplexity

#print axioms JointThermoComplexity.literal_path_necessary

#print axioms JointThermoComplexity.literal_path_construct

#print axioms JointThermoComplexity.literal_two_path_iff
