module
public import proofs.JointThermoComplexity.Complexity.NetworkGateCount
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! Charge actual gate-count-pass transitions to the canonical binary input length. -/

namespace JointThermoComplexity.Complexity.GateCountRuntime

theorem reaction_time_eq (n L : ℕ) :
    ReactionTally.timeBound n L = 2 * n * L + 14 * n + 2 * L + 14 := by
  unfold ReactionTally.timeBound
  ring1

theorem reaction_time_le {n R L : ℕ} (hn : n ≤ L) (hr : R ≤ L) :
    ReactionTally.timeBound n R ≤ 2 * L ^ 2 + 16 * L + 14 := by
  have hmul : n * R ≤ L * L :=
    (Nat.mul_le_mul_right R hn).trans (Nat.mul_le_mul_left L hr)
  have hprod := Nat.mul_le_mul_left 2 hmul
  rw [reaction_time_eq]
  have hbound : 2 * (n * R) + 14 * n + 2 * R + 14 ≤ 2 * (L * L) + 16 * L + 14 := by omega
  simpa only [Nat.mul_assoc, pow_two] using hbound

theorem network_tally_time_le (Q : NetworkCodec.Input) :
    NetworkTally.timeBound Q ≤ 2 * Q.code.length ^ 3 + 16 * Q.code.length ^ 2 + 18 * Q.code.length + 5 := by
  let L := Q.code.length
  have hd := NetworkCodec.dimensions_le_code_length Q
  have hn : Q.speciesCount ≤ L := by omega
  have hr : Q.reactionCount ≤ L := by omega
  have hprefix := NetworkTallyData.prefix_length_le Q
  have hrecords : (ReactionArrayData.code (NetworkTallyData.reactions Q)).length ≤ L := by
    simp only [List.length_append] at hprefix
    omega
  have ht := reaction_time_le hn hrecords
  have harray : Q.reactionCount *
      (ReactionTally.timeBound Q.speciesCount (ReactionArrayData.code (NetworkTallyData.reactions Q)).length + 2) +
      (Q.reactionCount + 2) ≤ 2 * L ^ 3 + 16 * L ^ 2 + 17 * L + 2 := by
    calc
      _ ≤ Q.reactionCount * (2 * L ^ 2 + 16 * L + 16) + (Q.reactionCount + 2) := by
        exact Nat.add_le_add_right (Nat.mul_le_mul_left Q.reactionCount (by omega)) (Q.reactionCount + 2)
      _ ≤ L * (2 * L ^ 2 + 16 * L + 16) + (L + 2) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hr) (Nat.add_le_add_right hr 2)
      _ = _ := by ring1
  unfold NetworkTally.timeBound
  change _ ≤ 2 * L ^ 3 + 16 * L ^ 2 + 18 * L + 5
  omega

theorem timeBound_le_input (Q : NetworkCodec.Input) :
    NetworkGateCount.timeBound Q ≤ 2 * Q.code.length ^ 3 + 16 * Q.code.length ^ 2 + 22 * Q.code.length + 13 := by
  have ht := network_tally_time_le Q
  have hg := InputSize.gates_le_input_length Q
  have hp := NetworkTallyData.prefix_length_le Q
  unfold NetworkGateCount.timeBound NetworkGateCount.scanned
  omega

end JointThermoComplexity.Complexity.GateCountRuntime

#print axioms JointThermoComplexity.Complexity.GateCountRuntime.timeBound_le_input
