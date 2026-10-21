module
public import proofs.JointThermoComplexity.Complexity.NetworkNumbering

set_option autoImplicit false
@[expose] public section

/-! Exact circuit gate counts from exponent payload bits, without numeric expansion. -/

namespace JointThermoComplexity.Complexity.ExactGateCount
open RealCircuit ReactionCircuit NetworkData

variable {n k r c : ℕ}

def bitsCost : List Bool → ℕ
  | [] => 0
  | bit :: rest => (if bit then 2 else 1) + bitsCost rest

theorem bitsCost_le (bits : List Bool) : bitsCost bits ≤ 2 * bits.length := by
  induction bits with
  | nil => simp [bitsCost]
  | cons bit rest ih => cases bit <;> simp [bitsCost] <;> omega

theorem power_run_size (s : BinaryPower.State n) (bits : List Bool) :
    (s.runBits bits).size = s.size + bitsCost bits := by
  induction bits generalizing s with
  | nil => simp [BinaryPower.State.runBits, bitsCost]
  | cons bit rest ih =>
    rw [BinaryPower.State.runBits, ih]
    cases bit <;> simp [BinaryPower.State.advance, bitsCost] <;> omega

theorem power_size (circuit : Circuit n k) (base : Fin k) (exponent : ℕ) :
    (BinaryPower.build circuit base exponent).size = k + 1 + bitsCost exponent.bits := by
  simpa only [BinaryPower.build, BinaryPower.start] using power_run_size (BinaryPower.start circuit base) exponent.bits

def monomialCost : List (Fin n × ℕ) → ℕ
  | [] => 0
  | item :: rest => (3 + bitsCost item.2.bits) + monomialCost rest

theorem monomial_advance_size (s : MonomialCircuit.State n) (item : Fin n × ℕ) :
    (s.advance item).size = s.size + (3 + bitsCost item.2.bits) := by
  simp only [MonomialCircuit.State.advance]
  rw [power_size]
  omega

theorem monomial_run_size (s : MonomialCircuit.State n) (items : List (Fin n × ℕ)) :
    (s.runTerms items).size = s.size + monomialCost items := by
  induction items generalizing s with
  | nil => simp [MonomialCircuit.State.runTerms, monomialCost]
  | cons item rest ih =>
    rw [MonomialCircuit.State.runTerms, ih, monomial_advance_size]
    simp only [monomialCost]
    omega

theorem monomial_size (circuit : Circuit n k) (items : List (Fin n × ℕ)) :
    (MonomialCircuit.build circuit items).size = k + 1 + monomialCost items := by
  simpa only [MonomialCircuit.build, MonomialCircuit.start] using
    monomial_run_size (MonomialCircuit.start circuit) items

def reactionCost (reaction : Reaction n) : ℕ :=
  6 + monomialCost (MonomialCircuit.denseTerms reaction.reactant) +
    monomialCost (MonomialCircuit.denseTerms reaction.product)

theorem reaction_size (circuit : Circuit n k) (reaction : Reaction n) :
    (ReactionCircuit.build circuit reaction).size = k + reactionCost reaction := by
  change (MonomialCircuit.build (MonomialCircuit.build circuit (MonomialCircuit.denseTerms reaction.reactant)).circuit
    (MonomialCircuit.denseTerms reaction.product)).size + 4 = _
  rw [monomial_size, monomial_size]
  unfold reactionCost
  omega

def networkCost : List (Reaction n) → ℕ
  | [] => 0
  | reaction :: rest => reactionCost reaction + networkCost rest

theorem network_advance_size (s : NetworkCircuit.State n) (reaction : Reaction n) :
    (s.advance reaction).size = s.size + reactionCost reaction := by
  exact reaction_size s.circuit reaction

theorem network_run_size (s : NetworkCircuit.State n) (reactions : List (Reaction n)) :
    (s.run reactions).size = s.size + networkCost reactions := by
  induction reactions generalizing s with
  | nil => simp [NetworkCircuit.State.run, networkCost]
  | cons reaction rest ih =>
    rw [NetworkCircuit.State.run, ih, network_advance_size]
    simp only [networkCost]
    omega

theorem network_build_size (reactions : List (Reaction n)) :
    (NetworkCircuit.build reactions).size = networkCost reactions := by
  simpa only [NetworkCircuit.build, Nat.zero_add] using
    network_run_size (⟨0, .nil, []⟩ : NetworkCircuit.State n) reactions

theorem gates_eq_cost (Q : Network n r c) :
    NetworkMembership.gates Q = networkCost (List.ofFn Q.reactions) := network_build_size _

end JointThermoComplexity.Complexity.ExactGateCount

#print axioms JointThermoComplexity.Complexity.ExactGateCount.gates_eq_cost
