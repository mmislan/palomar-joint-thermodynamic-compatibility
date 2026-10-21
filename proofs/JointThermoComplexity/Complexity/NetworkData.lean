module
public import proofs.JointThermoComplexity.Complexity.ReactionCircuit

set_option autoImplicit false
@[expose] public section

/-!
# Finite supplied-motif feasibility data

This total feasibility problem imposes no PAC recognition or side-incidence
test. Such structural requirements belong to the separate promised domain.
Activities and currents are global, while production is checked separately for
each supplied motif. Empty finite index sets retain their usual semantics.
-/

namespace JointThermoComplexity.Complexity.NetworkData
open ReactionCircuit
open scoped BigOperators

structure RationalPoint where
  numerator : ℤ
  denominator : ℕ
  denominator_pos : 0 < denominator

noncomputable def RationalPoint.value (q : RationalPoint) : ℝ :=
  (q.numerator : ℝ) / q.denominator

structure ClosedBox where
  lower : RationalPoint
  upper : RationalPoint

def ClosedBox.Contains (box : ClosedBox) (z : ℝ) : Prop :=
  (box.lower.numerator : ℝ) ≤ (box.lower.denominator : ℝ) * z ∧
    (box.upper.denominator : ℝ) * z ≤ (box.upper.numerator : ℝ)

theorem ClosedBox.contains_iff (box : ClosedBox) (z : ℝ) :
    box.Contains z ↔ box.lower.value ≤ z ∧ z ≤ box.upper.value := by
  have hl : (0 : ℝ) < box.lower.denominator := by exact_mod_cast box.lower.denominator_pos
  have hu : (0 : ℝ) < box.upper.denominator := by exact_mod_cast box.upper.denominator_pos
  simp only [ClosedBox.Contains, RationalPoint.value, div_le_iff₀ hl, le_div_iff₀ hu,
    mul_comm z]

structure Motif (n r : ℕ) where
  species : Finset (Fin n)
  reactions : Finset (Fin r)

structure Network (n r c : ℕ) where
  reactions : Fin r → Reaction n
  motifs : Fin c → Motif n r
  forward : Fin r → Bool
  boxes : Fin n → Option ClosedBox

variable {n r c : ℕ}

def stoich (reaction : Reaction n) (s : Fin n) : ℤ :=
  (reaction.product s : ℤ) - reaction.reactant s

def Network.production (Q : Network n r c) (a : Fin c) (s : Fin n)
    (j : Fin r → ℝ) : ℝ :=
  ∑ i, if i ∈ (Q.motifs a).reactions then (stoich (Q.reactions i) s : ℝ) * j i else 0

theorem Network.production_eq_sum (Q : Network n r c) (a : Fin c) (s : Fin n)
    (j : Fin r → ℝ) :
    Q.production a s j = ∑ i ∈ (Q.motifs a).reactions, (stoich (Q.reactions i) s : ℝ) * j i := by
  unfold Network.production
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

def direction (forward : Bool) (j : ℝ) : Prop := 0 < if forward then j else -j

def Network.Constraints (Q : Network n r c) (z : Fin n → ℝ) (j : Fin r → ℝ) : Prop :=
  (∀ s, 0 < z s) ∧
  (∀ s, match Q.boxes s with | none => True | some box => box.Contains (z s)) ∧
  ∀ a, (∀ i ∈ (Q.motifs a).reactions, direction (Q.forward i) (j i)) ∧
    ∀ s ∈ (Q.motifs a).species, 0 < Q.production a s j

def Network.Feasible (Q : Network n r c) : Prop :=
  ∃ z, Q.Constraints z (fun i => (Q.reactions i).current z)

def Network.CurrentEquations (Q : Network n r c) (z : Fin n → ℝ) (j : Fin r → ℝ) : Prop :=
  ∀ i, ((Q.reactions i).denominator : ℝ) * j i = numeratorValue i
where
  numeratorValue (i : Fin r) := (Q.reactions i).difference z * (Q.reactions i).numerator

theorem Network.currentEquations_iff (Q : Network n r c) (z : Fin n → ℝ)
    (j : Fin r → ℝ) :
    Q.CurrentEquations z j ↔ j = fun i => (Q.reactions i).current z := by
  constructor
  · intro h
    funext i
    exact (current_equation_iff (Q.reactions i) z (j i)).mp (h i)
  · intro h i
    rw [h]
    exact denominator_mul_current (Q.reactions i) z

theorem Network.exists_currents_iff (Q : Network n r c) :
    (∃ z j, Q.CurrentEquations z j ∧ Q.Constraints z j) ↔ Q.Feasible := by
  constructor
  · rintro ⟨z, j, heq, hc⟩
    have hj := (Q.currentEquations_iff z j).mp heq
    exact ⟨z, by simpa only [hj] using hc⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, _, (Q.currentEquations_iff z _).mpr rfl, hz⟩

end JointThermoComplexity.Complexity.NetworkData

#print axioms JointThermoComplexity.Complexity.NetworkData.ClosedBox.contains_iff
#print axioms JointThermoComplexity.Complexity.NetworkData.Network.production_eq_sum
#print axioms JointThermoComplexity.Complexity.NetworkData.Network.exists_currents_iff
