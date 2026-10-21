module
public import proofs.JointThermoComplexity.Complexity.ProductionFuelFrame
public import proofs.JointThermoComplexity.Complexity.ProductionDenseCode

set_option autoImplicit false
@[expose] public section

/-! The actual retained reaction-count loop emits the ordered add/selected-term stream with synchronized indices. -/

namespace JointThermoComplexity.Complexity.ProductionReactionLoop
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionReactionState ProductionFuelFrame InvariantLoop CurrentTraversal

def machine (m : ℕ) : TM (m + 20) := forRegTM (ProductionReactionStep.machine m) (fuel m)

def timeBound (L count : ℕ) : ℕ := count * (ProductionReactionStep.timeBound L + 2) + (count + 2)

def Invariant (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (s : Fin Q.speciesCount)
    (mask : Fin Q.reactionCount → Bool) (emitted : List Bool) (R : (Fin (m + 20) → Tape) → Prop) (i : ℕ) :
    _root_.Complexity.TapePred (m + 20) := fun inp work out =>
  Cursor [] input (emitted ++ output ((ProductionDenseCode.clauses Q s mask).take i)) inp work out ∧
    State m input.length Q.speciesCount i s.val (Q.speciesCount + i) (List.ofFn mask) i R work

theorem framed (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (s : Fin Q.speciesCount) (mask : Fin Q.reactionCount → Bool) (emitted : List Bool)
    (R : (Fin (m + 20) → Tape) → Prop)
    (hR : ∀ work work', Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (Frame (fuel m) Q.reactionCount 1 (Invariant m input Q s mask emitted R 0))
      (Frame (fuel m) Q.reactionCount 1 (Invariant m input Q s mask emitted R Q.reactionCount))
      (timeBound input.length Q.reactionCount) := by
  have hbody : ∀ i, i < Q.reactionCount → (ProductionReactionStep.machine m).HoareTime
      (Frame (fuel m) Q.reactionCount (i + 2) (Invariant m input Q s mask emitted R i))
      (Frame (fuel m) Q.reactionCount (i + 2) (Invariant m input Q s mask emitted R (i + 1)))
      (ProductionReactionStep.timeBound input.length) := by
    intro i hi
    let j : Fin Q.reactionCount := ⟨i, hi⟩
    have him : i < (List.ofFn mask).length := by simpa only [List.length_ofFn] using hi
    have hclause : i < (ProductionDenseCode.clauses Q s mask).length := by
      simpa only [ProductionDenseCode.clauses_length] using hi
    have hidx : (NetworkMembership.currentIndex Q.network j).val = Q.speciesCount + i := rfl
    have hs := ProductionFuelFrame.hoareTime m Q.reactionCount (i + 2) (by omega) input Q hd j s (List.ofFn mask) him
      (emitted ++ output ((ProductionDenseCode.clauses Q s mask).take i)) R hR
    exact hs.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, hidx, j] using hp.invariant) (by
        intro inp work out hp
        refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
        change Cursor [] input (emitted ++ output ((ProductionDenseCode.clauses Q s mask).take (i + 1))) inp
          (restore work (fuel m) Q.reactionCount) out ∧
          State m input.length Q.speciesCount (i + 1) s.val (Q.speciesCount + (i + 1)) (List.ofFn mask) (i + 1) R
            (restore work (fuel m) Q.reactionCount)
        rw [output_take_succ (ProductionDenseCode.clauses Q s mask) i hclause, ProductionDenseCode.clause_at Q s mask j]
        simpa only [List.append_assoc, hidx, j, Nat.add_assoc] using hp.invariant) le_rfl
  exact InvariantLoop.hoareTime (ProductionReactionStep.machine m) (fuel m)
    (Invariant m input Q s mask emitted R) (ProductionReactionStep.timeBound input.length) Q.reactionCount hbody

end JointThermoComplexity.Complexity.ProductionReactionLoop

#print axioms JointThermoComplexity.Complexity.ProductionReactionLoop.framed
