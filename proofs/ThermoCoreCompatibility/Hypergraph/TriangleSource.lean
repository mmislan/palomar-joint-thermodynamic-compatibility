module
public import proofs.ThermoCoreCompatibility.Source
public import proofs.ThermoCoreCompatibility.Hypergraph.PrivateTriangleBounds

set_option autoImplicit false
@[expose] public section

namespace ThermoCoreCompatibility.Hypergraph

open scoped BigOperators

def atom {S : Type*} [DecidableEq S] (s : S) (n : ℕ) : Complex S :=
  fun t => if t = s then n else 0

structure TriangleIn {S R : Type*} [DecidableEq S] [DecidableEq R]
    (Q : ReversibleCRN S R) where
  A : S
  B : S
  C : S
  AB : A ≠ B
  AC : A ≠ C
  BC : B ≠ C
  r₀ : R
  r₁ : R
  r₂ : R
  r01 : r₀ ≠ r₁
  r02 : r₀ ≠ r₂
  r12 : r₁ ≠ r₂
  gain : ℕ
  gain_ge_two : 2 ≤ gain
  react₀ : Q.reactant r₀ = atom A 1
  prod₀ : Q.product r₀ = atom B 1
  react₁ : Q.reactant r₁ = atom B 1
  prod₁ : Q.product r₁ = atom C 1
  react₂ : Q.reactant r₂ = atom C 1
  prod₂ : Q.product r₂ = atom A gain

variable {S R : Type*} [DecidableEq S] [DecidableEq R]
  {Q : ReversibleCRN S R}

def TriangleIn.motif (T : TriangleIn Q) : Motif Q where
  species := {T.A,T.B,T.C}
  reactions := {T.r₀,T.r₁,T.r₂}

theorem TriangleIn.balanceA (T : TriangleIn Q) (v : R → ℝ) :
    (∑ r ∈ T.motif.reactions, (Q.stoich T.A r : ℝ) * v r) =
      (T.gain : ℝ) * v T.r₂ - v T.r₀ := by
  simp [motif, ReversibleCRN.stoich, T.r01, T.r02, T.r12,
    T.react₀,T.react₁,T.react₂,T.prod₀,T.prod₁,T.prod₂,
    atom,T.AB,T.AC,sub_eq_add_neg,add_comm]

theorem TriangleIn.balanceB (T : TriangleIn Q) (v : R → ℝ) :
    (∑ r ∈ T.motif.reactions, (Q.stoich T.B r : ℝ) * v r) = v T.r₀-v T.r₁ := by
  simp [motif, ReversibleCRN.stoich, T.r01, T.r02, T.r12,
    T.react₀,T.react₁,T.react₂,T.prod₀,T.prod₁,T.prod₂,
    atom,Ne.symm T.AB,T.BC,sub_eq_add_neg]

theorem TriangleIn.balanceC (T : TriangleIn Q) (v : R → ℝ) :
    (∑ r ∈ T.motif.reactions, (Q.stoich T.C r : ℝ) * v r) = v T.r₁-v T.r₂ := by
  simp [motif, ReversibleCRN.stoich, T.r01, T.r02, T.r12,
    T.react₀,T.react₁,T.react₂,T.prod₀,T.prod₁,T.prod₂,
    atom,Ne.symm T.AC,Ne.symm T.BC,sub_eq_add_neg]

theorem TriangleIn.productive_iff (T : TriangleIn Q) (v : R → ℝ) :
    T.motif.Productive v ↔
      v T.r₀ < (T.gain : ℝ) * v T.r₂ ∧ v T.r₁ < v T.r₀ ∧ v T.r₂ < v T.r₁ := by
  simp only [Motif.Productive, motif, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq]
  change (0 < ∑ r ∈ T.motif.reactions, (Q.stoich T.A r : ℝ)*v r) ∧
    (0 < ∑ r ∈ T.motif.reactions, (Q.stoich T.B r : ℝ)*v r) ∧
    (0 < ∑ r ∈ T.motif.reactions, (Q.stoich T.C r : ℝ)*v r) ↔ _
  rw [T.balanceA, T.balanceB, T.balanceC]
  simp only [sub_pos]

theorem activity_atom [Fintype S] (z : S → ℝ) (s : S) (n : ℕ) :
    ReversibleCRN.complexActivity z (atom s n) = z s ^ n := by
  unfold ReversibleCRN.complexActivity
  rw [Finset.prod_eq_single s]
  · simp [atom]
  · intro t _ ht
    simp [atom,ht]
  · simp

theorem TriangleIn.current_production_iff [Fintype S] (T : TriangleIn Q) (z : S → ℝ) :
    T.motif.Productive (Q.current z) ↔
      TriangleProduction T.gain (Q.barrier T.r₁) (Q.barrier T.r₂)
        (z T.A ^ T.gain) (z T.B) (z T.C)
        (Q.barrier T.r₀ * (z T.A - z T.B)) := by
  rw [T.productive_iff]
  simp only [ReversibleCRN.current,T.react₀,T.react₁,T.react₂,
    T.prod₀,T.prod₁,T.prod₂,activity_atom,pow_one,TriangleProduction]

private theorem atom_endpoint {s : S} {n : ℕ} {ss : Finset S}
    (h : ∃ t ∈ ss, 0 < atom s n t) : s ∈ ss := by
  obtain ⟨t,ht,h⟩ := h
  unfold atom at h
  split_ifs at h with he
  · simpa [he] using ht
  · omega

theorem TriangleIn.sideIncident (T : TriangleIn Q) : T.motif.SideIncident := by
  refine ⟨⟨T.A, by simp [motif]⟩, ⟨T.r₀, by simp [motif]⟩, ?_⟩
  intro r hr
  simp only [motif,Finset.mem_insert,Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨T.A, by simp [motif], by simp [T.react₀,atom]⟩,
      ⟨T.B, by simp [motif], by simp [T.prod₀,atom]⟩⟩
  · exact ⟨⟨T.B, by simp [motif], by simp [T.react₁,atom]⟩,
      ⟨T.C, by simp [motif], by simp [T.prod₁,atom]⟩⟩
  · exact ⟨⟨T.C, by simp [motif], by simp [T.react₂,atom]⟩,
      ⟨T.A, by simp [motif], by simpa [T.prod₂,atom] using
        (lt_of_lt_of_le (by decide : 0 < 2) T.gain_ge_two)⟩⟩

private theorem masked_production (T : TriangleIn Q) (small : Motif Q)
    (hsub : small.reactions ⊆ T.motif.reactions) (v : R → ℝ) (s : S)
    (hp : small.Productive v) (hs : s ∈ small.species) :
    0 < ∑ r ∈ T.motif.reactions, (Q.stoich s r : ℝ) *
      (if r ∈ small.reactions then v r else 0) := by
  have he : (∑ r ∈ small.reactions, (Q.stoich s r : ℝ)*v r) =
      ∑ r ∈ T.motif.reactions, (Q.stoich s r : ℝ)*
        (if r ∈ small.reactions then v r else 0) := by
    calc
      _ = ∑ r ∈ small.reactions, (Q.stoich s r : ℝ)*
          (if r ∈ small.reactions then v r else 0) := by
        apply Finset.sum_congr rfl
        intro r hr
        simp [hr]
      _ = _ := Finset.sum_subset hsub (by intro r _ hr; simp [hr])
  rw [← he]
  exact hp s hs

private theorem support_complete (m : ℝ) (hm : 0 < m)
    (p q r : Prop) [Decidable p] [Decidable q] [Decidable r]
    (x y z : ℝ) (hne : p ∨ q ∨ r)
    (hpa : p → 0 < m*(if r then z else 0)-(if p then x else 0))
    (hpb : p → 0 < (if p then x else 0)-(if q then y else 0))
    (hqb : q → 0 < (if p then x else 0)-(if q then y else 0))
    (hqc : q → 0 < (if q then y else 0)-(if r then z else 0))
    (hrc : r → 0 < (if q then y else 0)-(if r then z else 0))
    (hra : r → 0 < m*(if r then z else 0)-(if p then x else 0)) : p ∧ q ∧ r := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
    simp_all <;> nlinarith

/-- Signed minimality: the proof places no positivity assumption on an
arbitrary productive flow of a putative strict submotif. -/
theorem TriangleIn.isPAC (T : TriangleIn Q) : T.motif.IsPAC := by
  have hm : (2 : ℝ) ≤ T.gain := by exact_mod_cast T.gain_ge_two
  constructor
  · refine ⟨T.sideIncident, (fun r => if r = T.r₀ then 1 else if r = T.r₁ then 5/6 else 2/3), ?_⟩
    rw [T.productive_iff]
    simp only [Ne.symm T.r01, Ne.symm T.r02, Ne.symm T.r12, ite_false]
    constructor
    · norm_num
      linarith
    · norm_num
  · intro small hstrict hauto
    obtain ⟨hside,v,hp⟩ := hauto
    have e₀ (h : T.r₀ ∈ small.reactions) : T.A ∈ small.species ∧ T.B ∈ small.species := by
      obtain ⟨hl,hr⟩ := hside.2.2 T.r₀ h
      rw [T.react₀] at hl
      rw [T.prod₀] at hr
      exact ⟨atom_endpoint hl,atom_endpoint hr⟩
    have e₁ (h : T.r₁ ∈ small.reactions) : T.B ∈ small.species ∧ T.C ∈ small.species := by
      obtain ⟨hl,hr⟩ := hside.2.2 T.r₁ h
      rw [T.react₁] at hl
      rw [T.prod₁] at hr
      exact ⟨atom_endpoint hl,atom_endpoint hr⟩
    have e₂ (h : T.r₂ ∈ small.reactions) : T.C ∈ small.species ∧ T.A ∈ small.species := by
      obtain ⟨hl,hr⟩ := hside.2.2 T.r₂ h
      rw [T.react₂] at hl
      rw [T.prod₂] at hr
      exact ⟨atom_endpoint hl,atom_endpoint hr⟩
    have hne : T.r₀ ∈ small.reactions ∨ T.r₁ ∈ small.reactions ∨ T.r₂ ∈ small.reactions := by
      obtain ⟨r,hr⟩ := hside.2.1
      have hh := hstrict.2.1 hr
      simp only [motif,Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with rfl | rfl | rfl <;> tauto
    have hA := fun hs => masked_production T small hstrict.2.1 v T.A hp hs
    have hB := fun hs => masked_production T small hstrict.2.1 v T.B hp hs
    have hC := fun hs => masked_production T small hstrict.2.1 v T.C hp hs
    simp only [T.balanceA] at hA
    simp only [T.balanceB] at hB
    simp only [T.balanceC] at hC
    have hall := support_complete (T.gain : ℝ) (by linarith)
      (T.r₀ ∈ small.reactions) (T.r₁ ∈ small.reactions) (T.r₂ ∈ small.reactions)
      (v T.r₀) (v T.r₁) (v T.r₂) hne
      (fun h => hA (e₀ h).1) (fun h => hB (e₀ h).2)
      (fun h => hB (e₁ h).1) (fun h => hC (e₁ h).2)
      (fun h => hC (e₂ h).1) (fun h => hA (e₂ h).2)
    have hr : small.reactions = T.motif.reactions := by
      apply Finset.Subset.antisymm hstrict.2.1
      intro r hr
      simp only [motif,Finset.mem_insert,Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact hall.1
      · exact hall.2.1
      · exact hall.2.2
    have hs : small.species = T.motif.species := by
      apply Finset.Subset.antisymm hstrict.1
      intro s hs
      simp only [motif,Finset.mem_insert,Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl
      · exact (e₀ hall.1).1
      · exact (e₀ hall.1).2
      · exact (e₁ hall.2.1).2
    exact hstrict.2.2.elim (fun h => h hs) (fun h => h hr)

end ThermoCoreCompatibility.Hypergraph

#print axioms ThermoCoreCompatibility.Hypergraph.TriangleIn.isPAC

#print axioms ThermoCoreCompatibility.Hypergraph.TriangleIn.current_production_iff
