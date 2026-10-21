module
public import proofs.JointThermoComplexity.Complexity.NetworkMembership
public import proofs.ThermoCoreCompatibility.CoreFamily

set_option autoImplicit false
@[expose] public section

/-!
# Bridge to the preserved literal chemistry model

The finite rational model has exactly the preserved reversible currents and
per-motif production predicates. On supplied PAC annotations covering every
reaction, unboxed total feasibility is the original CoreFamily.MultiCAC.
PAC status is a separate hypothesis here, never inferred from real feasibility.
-/

namespace JointThermoComplexity.Complexity.LiteralBridge
open NetworkData

noncomputable section
variable {n r c : ℕ}

def toCRN (Q : Network n r c) : ThermoCoreCompatibility.ReversibleCRN (Fin n) (Fin r) where
  reactant i := (Q.reactions i).reactant
  product i := (Q.reactions i).product
  barrier i := ((Q.reactions i).numerator : ℝ) / (Q.reactions i).denominator
  barrier_pos i := div_pos (by exact_mod_cast (Q.reactions i).numerator_pos)
    (by exact_mod_cast (Q.reactions i).denominator_pos)

def toMotif (Q : Network n r c) (a : Fin c) : ThermoCoreCompatibility.Motif (toCRN Q) where
  species := (Q.motifs a).species
  reactions := (Q.motifs a).reactions

def orientation (Q : Network n r c) (i : Fin r) : ℤ := if Q.forward i then 1 else -1

theorem current_eq (Q : Network n r c) (z : Fin n → ℝ) (i : Fin r) :
    (toCRN Q).current z i = (Q.reactions i).current z := rfl

theorem stoich_eq (Q : Network n r c) (s : Fin n) (i : Fin r) :
    (toCRN Q).stoich s i = stoich (Q.reactions i) s := rfl

theorem productive_iff (Q : Network n r c) (a : Fin c) (j : Fin r → ℝ) :
    (toMotif Q a).Productive j ↔ ∀ s ∈ (Q.motifs a).species, 0 < Q.production a s j := by
  simp only [ThermoCoreCompatibility.Motif.Productive, toMotif, Network.production_eq_sum]
  rfl

theorem direction_iff (Q : Network n r c) (i : Fin r) (j : ℝ) :
    direction (Q.forward i) j ↔ 0 < (orientation Q i : ℝ) * j := by
  cases h : Q.forward i <;> simp [direction, orientation, h]

theorem constraints_iff (Q : Network n r c) (z : Fin n → ℝ) (j : Fin r → ℝ) :
    Q.Constraints z j ↔
      (∀ s, 0 < z s) ∧
      (∀ s, match Q.boxes s with | none => True | some box => box.Contains (z s)) ∧
      (∀ a, ∀ i ∈ (Q.motifs a).reactions, 0 < (orientation Q i : ℝ) * j i) ∧
      ∀ a, (toMotif Q a).Productive j := by
  simp only [Network.Constraints, direction_iff, productive_iff, forall_and]
  rfl

def toFamily (Q : Network n r c) (pac : ∀ a, (toMotif Q a).IsPAC)
    (owner : Fin r → Fin c) (covered : ∀ i, i ∈ (Q.motifs (owner i)).reactions) :
    ThermoCoreCompatibility.CoreFamily (Core := Fin c) (toCRN Q) where
  core := toMotif Q
  core_isPAC := pac
  orientation := orientation Q
  orientation_unit i := by cases h : Q.forward i <;> simp [orientation, h]
  owner := owner
  owner_mem := covered

theorem constraints_family_iff (Q : Network n r c) (pac : ∀ a, (toMotif Q a).IsPAC)
    (owner : Fin r → Fin c) (covered : ∀ i, i ∈ (Q.motifs (owner i)).reactions)
    (z : Fin n → ℝ) (j : Fin r → ℝ) :
    Q.Constraints z j ↔
      (∀ s, 0 < z s) ∧
      (∀ s, match Q.boxes s with | none => True | some box => box.Contains (z s)) ∧
      (∀ i, 0 < ((toFamily Q pac owner covered).orientation i : ℝ) * j i) ∧
      ∀ a, ((toFamily Q pac owner covered).core a).Productive j := by
  rw [constraints_iff]
  constructor
  · rintro ⟨hz, hb, hd, hp⟩
    refine ⟨hz, hb, ?_, hp⟩
    intro i
    exact hd (owner i) i (covered i)
  · rintro ⟨hz, hb, hd, hp⟩
    refine ⟨hz, hb, ?_, hp⟩
    intro a i _
    exact hd i

theorem feasible_iff (Q : Network n r c) (pac : ∀ a, (toMotif Q a).IsPAC)
    (owner : Fin r → Fin c) (covered : ∀ i, i ∈ (Q.motifs (owner i)).reactions) :
    Q.Feasible ↔ ∃ z : Fin n → ℝ,
      (∀ s, 0 < z s) ∧
      (∀ s, match Q.boxes s with | none => True | some box => box.Contains (z s)) ∧
      (∀ i, 0 < ((toFamily Q pac owner covered).orientation i : ℝ) * (toCRN Q).current z i) ∧
      ∀ a, ((toFamily Q pac owner covered).core a).Productive ((toCRN Q).current z) := by
  exact exists_congr (fun z => constraints_family_iff Q pac owner covered z _)

theorem unboxed_iff_multiCAC (Q : Network n r c) (pac : ∀ a, (toMotif Q a).IsPAC)
    (owner : Fin r → Fin c) (covered : ∀ i, i ∈ (Q.motifs (owner i)).reactions)
    (unboxed : ∀ s, Q.boxes s = none) :
    Q.Feasible ↔ (toFamily Q pac owner covered).MultiCAC := by
  simpa [ThermoCoreCompatibility.CoreFamily.MultiCAC, unboxed] using feasible_iff Q pac owner covered

theorem code_mem_iff_multiCAC (Q : Network n r c) (pac : ∀ a, (toMotif Q a).IsPAC)
    (owner : Fin r → Fin c) (covered : ∀ i, i ∈ (Q.motifs (owner i)).reactions)
    (unboxed : ∀ s, Q.boxes s = none) :
    (NetworkMembership.sentence Q).code ∈ RealSyntax.ETR ↔
      (toFamily Q pac owner covered).MultiCAC :=
  (NetworkMembership.code_mem_ETR_iff Q).trans
    (unboxed_iff_multiCAC Q pac owner covered unboxed)

end
end JointThermoComplexity.Complexity.LiteralBridge

#print axioms JointThermoComplexity.Complexity.LiteralBridge.current_eq
#print axioms JointThermoComplexity.Complexity.LiteralBridge.productive_iff
#print axioms JointThermoComplexity.Complexity.LiteralBridge.feasible_iff
#print axioms JointThermoComplexity.Complexity.LiteralBridge.code_mem_iff_multiCAC
