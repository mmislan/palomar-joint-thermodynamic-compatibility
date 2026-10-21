module
public import proofs.JointThermoComplexity.Complexity.RationalLiteralIdentity

set_option autoImplicit false
@[expose] public section

/-! Per-core production and global direction constraints under the exact
reaction numbering. The same flux/state is used for both supplied motifs. -/

namespace JointThermoComplexity.Complexity.RationalLiteralProduction
open RationalBranchData RationalLiteralNetwork RationalLiteralIdentity
variable {e n m : ℕ}

theorem productive_left_iff (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m)
    (v : Fin (reactionCount n m) → ℝ) :
    (LiteralBridge.toMotif (network boxed L R) 0).Productive v ↔
      (Emitted.leftCycle L.toBranch R.toBranch).motif.Productive (v ∘ reactionNumbering n m) := by
  change (RationalLiteralIdentity.leftCycle boxed L R).motif.Productive v ↔ _
  rw [(RationalLiteralIdentity.leftCycle boxed L R).productive_iff_chain,
    (Emitted.leftCycle L.toBranch R.toBranch).productive_iff_chain]
  rfl

theorem productive_right_iff (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m)
    (v : Fin (reactionCount n m) → ℝ) :
    (LiteralBridge.toMotif (network boxed L R) 1).Productive v ↔
      (Emitted.rightCycle L.toBranch R.toBranch).motif.Productive (v ∘ reactionNumbering n m) := by
  change (RationalLiteralIdentity.rightCycle boxed L R).motif.Productive v ↔ _
  rw [(RationalLiteralIdentity.rightCycle boxed L R).productive_iff_chain,
    (Emitted.rightCycle L.toBranch R.toBranch).productive_iff_chain]
  rfl

theorem productive_pair_iff (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m)
    (v : Fin (reactionCount n m) → ℝ) :
    (∀ a : Fin 2, (LiteralBridge.toMotif (network boxed L R) a).Productive v) ↔
      (Emitted.leftCycle L.toBranch R.toBranch).motif.Productive (v ∘ reactionNumbering n m) ∧
      (Emitted.rightCycle L.toBranch R.toBranch).motif.Productive (v ∘ reactionNumbering n m) := by
  constructor
  · intro h
    exact ⟨(productive_left_iff boxed L R v).mp (h 0), (productive_right_iff boxed L R v).mp (h 1)⟩
  · rintro ⟨hl, hr⟩ a
    fin_cases a
    · exact (productive_left_iff boxed L R v).mpr hl
    · exact (productive_right_iff boxed L R v).mpr hr

theorem positive_on_motifs_iff (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m)
    (v : Fin (reactionCount n m) → ℝ) :
    (∀ a : Fin 2, ∀ r ∈ ((network boxed L R).motifs a).reactions, 0 < v r) ↔ ∀ r, 0 < v r := by
  constructor
  · intro h r
    exact h (owner r) r (owner_mem boxed L R r)
  · intro h _ r _
    exact h r

theorem current_pull (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m)
    (z : Fin (speciesCount e n m) → ℝ) :
    (fun r => ((network boxed L R).reactions r).current z) ∘ reactionNumbering n m =
      (Emitted.source L.toBranch R.toBranch).current (z ∘ speciesNumbering e n m) := by
  funext r
  exact current_eq boxed L R z r

theorem currents_positive_iff (boxed : Bool) (L : Data (Fin e) n) (R : Data (Fin e) m)
    (z : Fin (speciesCount e n m) → ℝ) :
    (∀ r, 0 < ((network boxed L R).reactions r).current z) ↔
      ∀ r, 0 < (Emitted.source L.toBranch R.toBranch).current (z ∘ speciesNumbering e n m) r := by
  constructor
  · intro h r
    rw [← current_eq]
    exact h _
  · intro h r
    obtain ⟨r, rfl⟩ := (reactionNumbering n m).surjective r
    rw [current_eq]
    exact h r

theorem positive_states_iff (z : Fin (speciesCount e n m) → ℝ) :
    (∀ s, 0 < z s) ↔ ∀ s : Species e n m, 0 < (z ∘ speciesNumbering e n m) s := by
  constructor
  · intro h s
    exact h _
  · intro h s
    obtain ⟨s, rfl⟩ := (speciesNumbering e n m).surjective s
    exact h s

end JointThermoComplexity.Complexity.RationalLiteralProduction

#print axioms JointThermoComplexity.Complexity.RationalLiteralProduction.productive_pair_iff
#print axioms JointThermoComplexity.Complexity.RationalLiteralProduction.positive_on_motifs_iff
#print axioms JointThermoComplexity.Complexity.RationalLiteralProduction.currents_positive_iff
