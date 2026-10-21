module
public import proofs.JointThermoComplexity.EmittedSemantics

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity.Emitted
open ThermoCoreCompatibility
open scoped BigOperators
noncomputable section
variable {E : Type*} [Fintype E] [DecidableEq E] {n m : ℕ}

def Compatible (L : Branch E n) (R : Branch E m) (u : E→ℝ) : Prop :=
  ∃ z : Species E n m→ℝ, (∀s,0<z s) ∧ (∀e,z (external e)=u e) ∧
    (∀r,0<(source L R).current z r) ∧
    (leftCycle L R).motif.Productive ((source L R).current z) ∧
    (rightCycle L R).motif.Productive ((source L R).current z)

omit [Fintype E] [DecidableEq E] in
theorem right_zero : @rightVertex E n m 0=leftVertex 0 := by simp [rightVertex,leftVertex]
omit [Fintype E] [DecidableEq E] in
theorem right_one : @rightVertex E n m 1=leftVertex 1 := by simp [rightVertex,leftVertex]

omit [Fintype E] [DecidableEq E] in
theorem chain_positive {k : ℕ} (f : Fin (k+2)→ℝ) (ha : StrictAnti f)
    (hg : f 0<2*f (Fin.last (k+1))) : ∀i,0<f i := by
  obtain ⟨h0,hb⟩:=chain_bounds f ha hg
  intro i
  by_cases hi : i=0
  · simpa [hi] using h0
  · obtain ⟨j,rfl⟩:=Fin.exists_succ_eq.mpr hi
    linarith [(hb j).1]

theorem compatible_iff_resistances (L : Branch E n) (R : Branch E m)
    (u : E→ℝ) (hu : ∀e,0<u e) :
    Compatible L R u ↔
      (∑i,L.weight u i)<2*(∑i,R.weight u i) ∧
      (∑i,R.weight u i)<2*(∑i,L.weight u i) := by
  rw [← literal_two_path_iff (by omega) (by omega) (L.weight u) (R.weight u)
    (L.weight_pos u hu) (R.weight_pos u hu)]
  constructor
  · rintro ⟨z,hz,he,_,hL,hR⟩
    have hl:=(leftCycle L R).productive_iff_chain ((source L R).current z) |>.mp hL
    have hr:=(rightCycle L R).productive_iff_chain ((source L R).current z) |>.mp hR
    change StrictAnti (fun i=>(source L R).current z (.inl i)) ∧ _ at hl
    change StrictAnti (fun i=>(source L R).current z (.inr i)) ∧ _ at hr
    dsimp only [leftCycle] at hl
    dsimp only [rightCycle] at hr
    simp_rw [left_flux L R u hu z he] at hl
    simp_rw [right_flux L R u hu z he] at hr
    have pl:=productive_cycle_to_path (L.weight u) (fun i=>z (leftVertex i)) (fun _=>hz _) hl.1 hl.2
    have pr:=productive_cycle_to_path (R.weight u) (fun i=>z (rightVertex i)) (fun _=>hz _) hr.1 hr.2
    simp only [right_zero,right_one] at pr
    exact ⟨z (leftVertex 0),z (leftVertex 1),_,_,hz _,pl,pr⟩
  · rintro ⟨A,B,x,y,hA,hx,hy⟩
    obtain ⟨hp,ha,hg⟩:=path_to_productive_cycle (L.weight u) A B x hA hx
    obtain ⟨hq,hb,hh⟩:=path_to_productive_cycle (R.weight u) A B y hA hy
    let p : Fin (n+2)→ℝ:=cycleValues A x
    let q : Fin (m+2)→ℝ:=cycleValues A y
    have h0 : p 0=q 0 := by simp [p,q,cycleValues]
    have h1 : p 1=q 1 := by simpa [p,q,cycleValues] using hx.1.trans hy.1.symm
    let z:=assemble u p q
    have he : ∀e,z (external e)=u e := fun _=>rfl
    have hl (i) : (source L R).current z (.inl i)=cycleFlux (L.weight u) p i :=
      left_flux L R u hu z he i
    have hr (i) : (source L R).current z (.inr i)=cycleFlux (R.weight u) q i := by
      rw [right_flux L R u hu z he]
      have hv : (fun j=>z (rightVertex j))=q := funext (assemble_right u p q h0 h1)
      rw [hv]
    refine ⟨z,?_,he,?_,?_,?_⟩
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
      change StrictAnti (fun i=>(source L R).current z (.inl i)) ∧ _
      dsimp only [leftCycle]
      simp_rw [hl]
      exact ⟨ha,hg⟩
    · apply (rightCycle L R).productive_iff_chain _ |>.mpr
      change StrictAnti (fun i=>(source L R).current z (.inr i)) ∧ _
      dsimp only [rightCycle]
      simp_rw [hr]
      exact ⟨hb,hh⟩

end
end JointThermoComplexity.Emitted

#print axioms JointThermoComplexity.Emitted.compatible_iff_resistances
