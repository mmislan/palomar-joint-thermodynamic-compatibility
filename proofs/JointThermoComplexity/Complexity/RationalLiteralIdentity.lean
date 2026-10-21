module
public import proofs.JointThermoComplexity.Complexity.RationalLiteralNetwork
public import proofs.JointThermoComplexity.Complexity.LiteralBridge
public import Mathlib.Tactic.FinCases

set_option autoImplicit false
@[expose] public section

/-! Exact source identity under explicit finite numberings, one shared state,
and unconditional PAC proofs for the two supplied finite motifs. -/

namespace JointThermoComplexity.Complexity.RationalLiteralIdentity
open RationalBranchData RationalLiteralNetwork
open scoped BigOperators
variable {e n m : ℕ}

theorem reactant_raw_eq (L : Data (Fin e) n) (R : Data (Fin e) m) (r : Reaction n m) (s : Species e n m) :
    reactantRaw L R r s = (Emitted.source L.toBranch R.toBranch).reactant r s := by
  cases r <;> rcases s with i | (a | j) <;>
    simp only [reactantRaw, Emitted.source, atom, ThermoCoreCompatibility.Hypergraph.atom,
      padding, Emitted.padding, leftVertex, Emitted.leftVertex, rightVertex, Emitted.rightVertex,
      RationalBranchData.Data.powers, Emitted.Branch.powers, RationalBranchData.Data.toBranch]
  all_goals split_ifs <;> rfl

theorem product_raw_eq (L : Data (Fin e) n) (R : Data (Fin e) m) (r : Reaction n m) (s : Species e n m) :
    productRaw L R r s = (Emitted.source L.toBranch R.toBranch).product r s := by
  cases r <;> rcases s with i | (a | j) <;>
    simp only [productRaw, Emitted.source, atom, ThermoCoreCompatibility.Hypergraph.atom,
      padding, Emitted.padding, leftVertex, Emitted.leftVertex, rightVertex, Emitted.rightVertex,
      gain, cycleGain, RationalBranchData.Data.powers, Emitted.Branch.powers, RationalBranchData.Data.toBranch]
  all_goals split_ifs <;> rfl

theorem factor_raw_eq (L : Data (Fin e) n) (R : Data (Fin e) m) (r : Reaction n m) :
    (numeratorRaw L R r : ℝ) / denominatorRaw L R r = (Emitted.source L.toBranch R.toBranch).barrier r := by
  cases r with
  | inl i => exact (L.barrier_eq i).symm
  | inr i => exact (R.barrier_eq i).symm

theorem numbered_reactant (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m)
    (r : Reaction n m) (s : Species e n m) :
    ((network boxed L R).reactions (reactionNumbering n m r)).reactant (speciesNumbering e n m s) =
      (Emitted.source L.toBranch R.toBranch).reactant r s := by
  simpa only [network, reaction, Equiv.symm_apply_apply] using reactant_raw_eq L R r s

theorem numbered_product (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m)
    (r : Reaction n m) (s : Species e n m) :
    ((network boxed L R).reactions (reactionNumbering n m r)).product (speciesNumbering e n m s) =
      (Emitted.source L.toBranch R.toBranch).product r s := by
  simpa only [network, reaction, Equiv.symm_apply_apply] using product_raw_eq L R r s

theorem numbered_factor (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) (r : Reaction n m) :
    (((network boxed L R).reactions (reactionNumbering n m r)).numerator : ℝ) /
      ((network boxed L R).reactions (reactionNumbering n m r)).denominator =
      (Emitted.source L.toBranch R.toBranch).barrier r := by
  simpa only [network, reaction, Equiv.symm_apply_apply] using factor_raw_eq L R r

theorem rightVertex_injective : Function.Injective (@rightVertex e n m) := Emitted.rightVertex_injective

def leftCycle (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) :
    CycleIn (LiteralBridge.toCRN (network boxed L R)) n where
  vertex i := speciesNumbering e n m (leftVertex i)
  edge i := reactionNumbering n m (.inl i)
  vertex_injective := (speciesNumbering e n m).injective.comp Sum.inl_injective
  edge_injective := (reactionNumbering n m).injective.comp Sum.inl_injective
  reactant_on := by
    intro i j
    change ((network boxed L R).reactions (reactionNumbering n m (.inl i))).reactant
      (speciesNumbering e n m (leftVertex j)) = _
    rw [numbered_reactant]
    exact (Emitted.leftCycle L.toBranch R.toBranch).reactant_on i j
  product_on := by
    intro i j
    change ((network boxed L R).reactions (reactionNumbering n m (.inl i))).product
      (speciesNumbering e n m (leftVertex j)) = _
    rw [numbered_product]
    exact (Emitted.leftCycle L.toBranch R.toBranch).product_on i j

def rightCycle (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) :
    CycleIn (LiteralBridge.toCRN (network boxed L R)) m where
  vertex i := speciesNumbering e n m (rightVertex i)
  edge i := reactionNumbering n m (.inr i)
  vertex_injective := (speciesNumbering e n m).injective.comp rightVertex_injective
  edge_injective := (reactionNumbering n m).injective.comp Sum.inr_injective
  reactant_on := by
    intro i j
    change ((network boxed L R).reactions (reactionNumbering n m (.inr i))).reactant
      (speciesNumbering e n m (rightVertex j)) = _
    rw [numbered_reactant]
    exact (Emitted.rightCycle L.toBranch R.toBranch).reactant_on i j
  product_on := by
    intro i j
    change ((network boxed L R).reactions (reactionNumbering n m (.inr i))).product
      (speciesNumbering e n m (rightVertex j)) = _
    rw [numbered_product]
    exact (Emitted.rightCycle L.toBranch R.toBranch).product_on i j

theorem supplied_PACs (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) :
    ∀ a : Fin 2, (LiteralBridge.toMotif (network boxed L R) a).IsPAC := by
  intro a
  fin_cases a
  · exact (leftCycle boxed L R).isPAC
  · exact (rightCycle boxed L R).isPAC

def owner (r : Fin (reactionCount n m)) : Fin 2 :=
  match (reactionNumbering n m).symm r with | .inl _ => 0 | .inr _ => 1

theorem owner_mem (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m) (r : Fin (reactionCount n m)) :
    r ∈ ((network boxed L R).motifs (owner r)).reactions := by
  obtain ⟨r, rfl⟩ := (reactionNumbering n m).surjective r
  cases r <;> simp [owner, network, leftMotif, rightMotif]

theorem current_eq (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m)
    (z : Fin (speciesCount e n m) → ℝ) (r : Reaction n m) :
    ((network boxed L R).reactions (reactionNumbering n m r)).current z =
      (Emitted.source L.toBranch R.toBranch).current (z ∘ speciesNumbering e n m) r := by
  have ha : (∏ s : Fin (speciesCount e n m), z s ^
        ((network boxed L R).reactions (reactionNumbering n m r)).reactant s) =
      ∏ s : Species e n m, z (speciesNumbering e n m s) ^
        (Emitted.source L.toBranch R.toBranch).reactant r s := by
    simpa only [numbered_reactant] using
      ((speciesNumbering e n m).prod_comp (fun s => z s ^
        ((network boxed L R).reactions (reactionNumbering n m r)).reactant s)).symm
  have hb : (∏ s : Fin (speciesCount e n m), z s ^
        ((network boxed L R).reactions (reactionNumbering n m r)).product s) =
      ∏ s : Species e n m, z (speciesNumbering e n m s) ^
        (Emitted.source L.toBranch R.toBranch).product r s := by
    simpa only [numbered_product] using
      ((speciesNumbering e n m).prod_comp (fun s => z s ^
        ((network boxed L R).reactions (reactionNumbering n m r)).product s)).symm
  change ((((network boxed L R).reactions (reactionNumbering n m r)).numerator : ℝ) /
      ((network boxed L R).reactions (reactionNumbering n m r)).denominator) *
      ((∏ s, z s ^ ((network boxed L R).reactions (reactionNumbering n m r)).reactant s) -
       (∏ s, z s ^ ((network boxed L R).reactions (reactionNumbering n m r)).product s)) = _
  rw [numbered_factor, ha, hb]
  rfl

end JointThermoComplexity.Complexity.RationalLiteralIdentity

#print axioms JointThermoComplexity.Complexity.RationalLiteralIdentity.numbered_reactant
#print axioms JointThermoComplexity.Complexity.RationalLiteralIdentity.numbered_factor
#print axioms JointThermoComplexity.Complexity.RationalLiteralIdentity.supplied_PACs
#print axioms JointThermoComplexity.Complexity.RationalLiteralIdentity.owner_mem
#print axioms JointThermoComplexity.Complexity.RationalLiteralIdentity.current_eq
