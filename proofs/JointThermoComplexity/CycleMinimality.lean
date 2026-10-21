module
public import proofs.ThermoCoreCompatibility.Source
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

set_option autoImplicit false
@[expose] public section

namespace JointThermoComplexity
open ThermoCoreCompatibility
open scoped BigOperators
noncomputable section

def cycleGain (n : ℕ) (i : Fin (n+2)) : ℕ := if i = Fin.last (n+1) then 2 else 1

/-- Literal internal side coefficients; arbitrary external padding is permitted. -/
structure CycleIn {S R : Type*} [DecidableEq S] [DecidableEq R]
    (Q : ReversibleCRN S R) (n : ℕ) where
  vertex : Fin (n+2) → S
  edge : Fin (n+2) → R
  vertex_injective : Function.Injective vertex
  edge_injective : Function.Injective edge
  reactant_on : ∀ i j, Q.reactant (edge i) (vertex j) = if j=i then 1 else 0
  product_on : ∀ i j, Q.product (edge i) (vertex j) =
    if j=finRotate (n+2) i then cycleGain n i else 0

variable {S R : Type*} [DecidableEq S] [DecidableEq R]
variable {Q : ReversibleCRN S R} {n : ℕ}

def CycleIn.motif (T : CycleIn Q n) : Motif Q where
  species := Finset.univ.image T.vertex
  reactions := Finset.univ.image T.edge

theorem CycleIn.stoich_on (T : CycleIn Q n) (i j : Fin (n+2)) :
    (Q.stoich (T.vertex j) (T.edge i) : ℝ) =
      (if j=finRotate (n+2) i then (cycleGain n i : ℝ) else 0) -
      (if j=i then 1 else 0) := by
  simp [ReversibleCRN.stoich, T.reactant_on, T.product_on]

theorem CycleIn.balance (T : CycleIn Q n) (v : R → ℝ) (j : Fin (n+2)) :
    (∑ r ∈ T.motif.reactions, (Q.stoich (T.vertex j) r : ℝ)*v r) =
      (cycleGain n ((finRotate (n+2)).symm j) : ℝ)*v (T.edge ((finRotate (n+2)).symm j)) - v (T.edge j) := by
  rw [show T.motif.reactions = Finset.univ.image T.edge from rfl,
    Finset.sum_image (fun a _ b _ h => T.edge_injective h)]
  simp_rw [T.stoich_on, sub_mul, ite_mul, zero_mul,
    ← Equiv.symm_apply_eq (finRotate (n+2))]
  simp [Finset.sum_sub_distrib]

theorem CycleIn.sideIncident (T : CycleIn Q n) : T.motif.SideIncident := by
  refine ⟨⟨T.vertex 0, by simp [motif]⟩, ⟨T.edge 0, by simp [motif]⟩, ?_⟩
  intro r hr
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
  refine ⟨⟨T.vertex i, by simp [motif], by simp [T.reactant_on]⟩,
    ⟨T.vertex (finRotate (n+2) i), by simp [motif], ?_⟩⟩
  rw [T.product_on]
  rw [ite_eq_left rfl]
  unfold cycleGain
  split_ifs <;> omega

theorem CycleIn.endpoints (T : CycleIn Q n) (D : Motif Q)
    (hs : D.species ⊆ T.motif.species) (hd : D.SideIncident)
    (i : Fin (n+2)) (hi : T.edge i ∈ D.reactions) :
    T.vertex i ∈ D.species ∧ T.vertex (finRotate (n+2) i) ∈ D.species := by
  obtain ⟨⟨s,hsD,ha⟩,⟨t,htD,hb⟩⟩ := hd.2.2 _ hi
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (hs hsD)
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp (hs htD)
  rw [T.reactant_on] at ha
  rw [T.product_on] at hb
  split_ifs at ha with hj
  · subst j
    constructor
    · exact hsD
    · split_ifs at hb with hk
      · subst k; exact htD
      · omega
  · omega

/-- Removing any edge gives an explicit positive conservation vector. -/
theorem cycle_cut_weight (k i : Fin (n+2)) (hi : i ≠ k) :
    (cycleGain n i : ℝ) * (if (finRotate (n+2) i).val ≤ k.val then 1 else 2) =
      (if i.val ≤ k.val then 1 else 2) := by
  by_cases hlast : i = Fin.last (n+1)
  · subst i
    have hk : k.val < n+1 := by
      have hk' := k.isLt
      have hne : k.val ≠ n+1 := by intro h; apply hi; apply Fin.ext; simpa using h.symm
      omega
    norm_num [cycleGain, finRotate_last, hk.not_ge]
  · have hne : i.val ≠ k.val := fun h => hi (Fin.ext h)
    have hrot : (finRotate (n+2) i).val = i.val+1 := coe_finRotate_of_ne_last hlast
    rw [hrot]
    have hg : cycleGain n i = 1 := ite_eq_right hlast
    rw [hg]
    norm_num only [Nat.cast_one, one_mul]
    have he : i.val+1 ≤ k.val ↔ i.val ≤ k.val := by omega
    simp only [he]

theorem CycleIn.no_proper_autocatalytic (T : CycleIn Q n) (D : Motif Q)
    (hsub : D.StrictSubmotif T.motif) : ¬ D.IsAutocatalyticMotif := by
  classical
  rintro ⟨hside,v,hprod⟩
  have hmissing : ∃ k : Fin (n+2), T.edge k ∉ D.reactions := by
    by_contra h
    push Not at h
    have hre : D.reactions = T.motif.reactions := by
      apply Finset.Subset.antisymm hsub.2.1
      intro r hr
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hr
      exact h i
    have hse : D.species = T.motif.species := by
      apply Finset.Subset.antisymm hsub.1
      intro s hs
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
      exact (T.endpoints D hsub.1 hside i (h i)).1
    exact hsub.2.2.elim (fun h => h hse) (fun h => h hre)
  obtain ⟨k,hk⟩ := hmissing
  let w : Fin (n+2) → ℝ := fun i => if i.val ≤ k.val then 1 else 2
  have hw (i) : 0 < w i := by dsimp [w]; split_ifs <;> norm_num
  have hcol (r : R) (hr : r ∈ D.reactions) :
      (∑ i, w i*(Q.stoich (T.vertex i) r : ℝ)) = 0 := by
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (hsub.2.1 hr)
    have hj : j ≠ k := by intro h; subst j; exact hk hr
    simp_rw [T.stoich_on, mul_sub, mul_ite, mul_zero, mul_one]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have he := cycle_cut_weight k j hj
    dsimp [w]
    nlinarith
  let p : Fin (n+2) → ℝ := fun i => ∑ r ∈ D.reactions, (Q.stoich (T.vertex i) r : ℝ)*v r
  have hpnonneg (i : Fin (n+2)) : 0 ≤ p i := by
    by_cases hi : T.vertex i ∈ D.species
    · exact le_of_lt (hprod _ hi)
    · have hz : p i=0 := by
        apply Finset.sum_eq_zero
        intro r hr
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (hsub.2.1 hr)
        have he := T.endpoints D hsub.1 hside j hr
        have h₁ : i ≠ j := by intro h; subst i; exact hi he.1
        have h₂ : i ≠ finRotate (n+2) j := by intro h; subst i; exact hi he.2
        rw [T.stoich_on]
        simp only [ite_eq_right h₁, ite_eq_right h₂, sub_self, zero_mul]
      rw [hz]
  have hpositive : 0 < ∑ i, w i*p i := by
    obtain ⟨s,hs⟩ := hside.1
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (hsub.1 hs)
    exact Finset.sum_pos' (fun j _ => mul_nonneg (le_of_lt (hw j)) (hpnonneg j))
      ⟨i, Finset.mem_univ _, mul_pos (hw i) (hprod _ hs)⟩
  have hzero : (∑ i, w i*p i)=0 := by
    simp only [p, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro r hr
    calc
      (∑ i, w i*((Q.stoich (T.vertex i) r : ℝ)*v r)) =
          (∑ i, w i*(Q.stoich (T.vertex i) r : ℝ))*v r := by rw [Finset.sum_mul]; congr 1; funext i; ring
      _ = 0 := by rw [hcol r hr, zero_mul]
  linarith

theorem CycleIn.isPAC (T : CycleIn Q n) : T.motif.IsPAC := by
  classical
  let d : ℝ := 2*((n:ℝ)+2)
  have hd : 0 < d := by dsimp [d]; positivity
  let f : Fin (n+2) → ℝ := fun i => 1-(i.val:ℝ)/d
  have hf (i) : d*f i=d-(i.val:ℝ) := by
    dsimp [f]
    field_simp
  have hp (i : Fin (n+2)) : 0 < (cycleGain n i : ℝ)*f i-f (finRotate (n+2) i) := by
    have h₁ := hf i
    have h₂ := hf (finRotate (n+2) i)
    apply (mul_pos_iff_of_pos_left hd).mp
    by_cases hi : i=Fin.last (n+1)
    · subst i
      norm_num [cycleGain, finRotate_last] at *
      dsimp [d] at *
      nlinarith
    · have he := coe_finRotate_of_ne_last hi
      have heR : ((finRotate (n+2) i).val:ℝ)=(i.val:ℝ)+1 := by exact_mod_cast he
      have hg : cycleGain n i = 1 := ite_eq_right hi
      rw [hg]
      norm_num only [Nat.cast_one, one_mul]
      nlinarith
  refine ⟨⟨T.sideIncident, Function.extend T.edge f (fun _ => 0), ?_⟩,
    fun D h => T.no_proper_autocatalytic D h⟩
  intro s hs
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨i,rfl⟩ := (finRotate (n+2)).surjective j
  rw [T.balance]
  simp only [Equiv.symm_apply_apply, T.edge_injective.extend_apply]
  exact hp i

theorem CycleIn.productive_iff_chain (T : CycleIn Q n) (v : R → ℝ) :
    T.motif.Productive v ↔
      StrictAnti (fun i => v (T.edge i)) ∧ v (T.edge 0)<2*v (T.edge (Fin.last (n+1))) := by
  have hrow (i : Fin (n+2)) :
      (∑ r ∈ T.motif.reactions, (Q.stoich (T.vertex (finRotate (n+2) i)) r : ℝ)*v r) =
        (cycleGain n i : ℝ)*v (T.edge i)-v (T.edge (finRotate (n+2) i)) := by
    rw [T.balance, Equiv.symm_apply_apply]
  constructor
  · intro hp
    constructor
    · apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      have h:=hp (T.vertex (finRotate (n+2) i.castSucc)) (by simp [motif])
      rw [hrow] at h
      have hr : finRotate (n+2) i.castSucc=i.succ := finRotate_of_lt i.isLt
      have hg : cycleGain n i.castSucc=1 := ite_eq_right (Fin.castSucc_ne_last i)
      rw [hg,hr] at h
      norm_num at h
      linarith
    · have h:=hp (T.vertex (finRotate (n+2) (Fin.last (n+1)))) (by simp [motif])
      rw [hrow] at h
      norm_num [cycleGain,finRotate_last] at h
      linarith
  · rintro ⟨ha,hg⟩ s hs
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨i,rfl⟩ := (finRotate (n+2)).surjective j
    rw [hrow]
    by_cases hi : i=Fin.last (n+1)
    · subst i
      norm_num [cycleGain,finRotate_last]
      linarith
    · have hgain : cycleGain n i=1 := ite_eq_right hi
      rw [hgain]
      norm_num only [Nat.cast_one,one_mul]
      exact sub_pos.mpr (ha ((lt_finRotate_iff_ne_last i).2 hi))

end
end JointThermoComplexity

#print axioms JointThermoComplexity.CycleIn.isPAC

#print axioms JointThermoComplexity.CycleIn.productive_iff_chain
