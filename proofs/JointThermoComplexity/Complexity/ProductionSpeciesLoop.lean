module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesFuelFrame
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesDenseCode

set_option autoImplicit false
@[expose] public section

/-! The actual copied-species register loop emits the ordered production-clause stream. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesLoop
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState ProductionSpeciesFuelFrame InvariantLoop CurrentTraversal

def machine (m : ℕ) : TM (m + 22) := forRegTM (ProductionSpeciesStep.machine m) (fuel m)

def timeBound (L count : ℕ) : ℕ := count * (ProductionSpeciesStep.timeBound L + 2) + (count + 2)

def Invariant (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (a : Fin Q.coreCount)
    (emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop) (i : ℕ) : _root_.Complexity.TapePred (m + 22) :=
  fun inp work out => Cursor [] input (emitted ++ output ((ProductionSpeciesDenseCode.clauses Q a).take i)) inp work out ∧
    State m input Q a i R work

theorem framed (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (Frame (fuel m) Q.speciesCount 1 (Invariant m input Q a emitted R 0))
      (Frame (fuel m) Q.speciesCount 1 (Invariant m input Q a emitted R Q.speciesCount))
      (timeBound input.length Q.speciesCount) := by
  have hbody : ∀ i, i < Q.speciesCount → (ProductionSpeciesStep.machine m).HoareTime
      (Frame (fuel m) Q.speciesCount (i + 2) (Invariant m input Q a emitted R i))
      (Frame (fuel m) Q.speciesCount (i + 2) (Invariant m input Q a emitted R (i + 1)))
      (ProductionSpeciesStep.timeBound input.length) := by
    intro i hi
    let s : Fin Q.speciesCount := ⟨i, hi⟩
    have hclause : i < (ProductionSpeciesDenseCode.clauses Q a).length := by
      simpa only [ProductionSpeciesDenseCode.clauses_length] using hi
    have hs := ProductionSpeciesFuelFrame.hoareTime m Q.speciesCount (i + 2) (by omega) input Q hd a s
      (emitted ++ output ((ProductionSpeciesDenseCode.clauses Q a).take i)) R hR
    exact hs.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, s] using hp.invariant) (by
        intro inp work out hp
        refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
        change Cursor [] input (emitted ++ output ((ProductionSpeciesDenseCode.clauses Q a).take (i + 1))) inp
          (restore work (fuel m) Q.speciesCount) out ∧ State m input Q a (i + 1) R (restore work (fuel m) Q.speciesCount)
        rw [output_take_succ (ProductionSpeciesDenseCode.clauses Q a) i hclause, ProductionSpeciesDenseCode.clause_at Q a s]
        simpa only [List.append_assoc, s] using hp.invariant) le_rfl
  exact InvariantLoop.hoareTime (ProductionSpeciesStep.machine m) (fuel m)
    (Invariant m input Q a emitted R) (ProductionSpeciesStep.timeBound input.length) Q.speciesCount hbody

end JointThermoComplexity.Complexity.ProductionSpeciesLoop

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesLoop.framed
