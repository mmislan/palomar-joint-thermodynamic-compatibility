module
public import proofs.JointThermoComplexity.Complexity.ProductionReactionLoop
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! Canonical count entry/exit and a quartic input-length bound for the actual production reaction loop. -/

namespace JointThermoComplexity.Complexity.ProductionReactionLoopEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionReactionState ProductionFuelFrame InvariantLoop CurrentTraversal

def timeBound (L : ℕ) : ℕ := 4 * L ^ 4 + 52 * L ^ 3 + 150 * L ^ 2 + 165 * L + 2

theorem runtime_bound (L n : ℕ) (hn : n ≤ L) : ProductionReactionLoop.timeBound L n ≤ timeBound L := by
  unfold ProductionReactionLoop.timeBound
  calc n * (ProductionReactionStep.timeBound L + 2) + (n + 2) ≤
       L * (ProductionReactionStep.timeBound L + 2) + (L + 2) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hn) (Nat.add_le_add_right hn 2)
       _ = _ := by unfold ProductionReactionStep.timeBound timeBound; ring1

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (s : Fin Q.speciesCount) (mask : Fin Q.reactionCount → Bool) (emitted : List Bool)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (ProductionReactionLoop.machine m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧
        State m input.length Q.speciesCount 0 s.val Q.speciesCount (List.ofFn mask) 0 R work ∧ IsReg Q.reactionCount (work (fuel m)))
      (fun inp work out => Cursor [] input (emitted ++ output (ProductionDenseCode.clauses Q s mask)) inp work out ∧
        State m input.length Q.speciesCount Q.reactionCount s.val (Q.speciesCount + Q.reactionCount)
          (List.ofFn mask) Q.reactionCount R work ∧ IsReg Q.reactionCount (work (fuel m))) (timeBound input.length) := by
  have hf := ProductionReactionLoop.framed m input Q hd s mask emitted R hR
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  exact hf.consequence (by
    rintro inp work out ⟨hc, hp, hr⟩
    refine ⟨hr.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work (fuel m) Q.reactionCount hr.eq_regT]
    simpa only [ProductionReactionLoop.Invariant, List.take_zero, output, List.flatMap_nil, List.append_nil, Nat.add_zero]
      using And.intro hc hp) (by
        intro inp work out hp
        have hclauses : (ProductionDenseCode.clauses Q s mask).take Q.reactionCount = ProductionDenseCode.clauses Q s mask := by
          rw [← ProductionDenseCode.clauses_length Q s mask, List.take_length]
        exact ⟨by simpa only [ProductionReactionLoop.Invariant, hclauses] using hp.on_work.1,
          hp.on_work.2, hp.register⟩) (runtime_bound input.length Q.reactionCount (by omega))

end JointThermoComplexity.Complexity.ProductionReactionLoopEntry

#print axioms JointThermoComplexity.Complexity.ProductionReactionLoopEntry.runtime_bound
#print axioms JointThermoComplexity.Complexity.ProductionReactionLoopEntry.hoareTime
