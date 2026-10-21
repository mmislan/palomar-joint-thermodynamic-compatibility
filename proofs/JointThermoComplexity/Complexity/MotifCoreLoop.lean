module
public import proofs.JointThermoComplexity.Complexity.MotifCoreFuelFrame
public import proofs.JointThermoComplexity.Complexity.MotifCoreDenseCode

set_option autoImplicit false
@[expose] public section

/-! The actual copied-core loop emits the complete ordered motif stream with reusable next-core state. -/

namespace JointThermoComplexity.Complexity.MotifCoreLoop
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifCoreState MotifCoreFuelFrame InvariantLoop CurrentTraversal

def machine (m : ℕ) : TM (m + 22) := forRegTM (MotifCoreStep.machine m) (fuel m)

def timeBound (L count : ℕ) : ℕ := count * (MotifCoreStep.timeBound L + 2) + (count + 2)

def Invariant (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (emitted : List Bool)
    (R : (Fin (m + 22) → Tape) → Prop) (i : ℕ) : _root_.Complexity.TapePred (m + 22) :=
  fun inp work out => Cursor [] input (emitted ++ output ((MotifCoreDenseCode.clauses Q).take i)) inp work out ∧
    State m input Q i R work ∧ IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0))

theorem framed (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', MotifCompleteFrame.Unchanged m work work' → R work → R work') :
    (machine m).HoareTime
      (Frame (fuel m) Q.coreCount 1 (Invariant m input Q emitted R 0))
      (Frame (fuel m) Q.coreCount 1 (Invariant m input Q emitted R Q.coreCount))
      (timeBound input.length Q.coreCount) := by
  have hb : ∀ i, i < Q.coreCount → (MotifCoreStep.machine m).HoareTime
      (Frame (fuel m) Q.coreCount (i + 2) (Invariant m input Q emitted R i))
      (Frame (fuel m) Q.coreCount (i + 2) (Invariant m input Q emitted R (i + 1))) (MotifCoreStep.timeBound input.length) := by
    intro i hi
    let a : Fin Q.coreCount := ⟨i, hi⟩
    have hclause : i < (MotifCoreDenseCode.clauses Q).length := by simpa only [MotifCoreDenseCode.clauses_length] using hi
    have hs := MotifCoreFuelFrame.hoareTime m Q.coreCount (i + 2) (by omega) input Q hd a
      (emitted ++ output ((MotifCoreDenseCode.clauses Q).take i)) R hR
    exact hs.consequence (by
      intro inp work out hp
      refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
      simpa only [Invariant, a] using hp.invariant) (by
        intro inp work out hp
        refine ⟨hp.fuel, hp.readInput, hp.readOthers, hp.readOutput, ?_⟩
        change Cursor [] input (emitted ++ output ((MotifCoreDenseCode.clauses Q).take (i + 1))) inp
          (restore work (fuel m) Q.coreCount) out ∧ State m input Q (i + 1) R (restore work (fuel m) Q.coreCount) ∧
          IsReg Q.speciesCount (restore work (fuel m) Q.coreCount (OuterFuelPorts.destination m 0))
        rw [output_take_succ (MotifCoreDenseCode.clauses Q) i hclause, MotifCoreDenseCode.clause_at Q a]
        simpa only [List.append_assoc, a] using hp.invariant) le_rfl
  exact InvariantLoop.hoareTime (MotifCoreStep.machine m) (fuel m)
    (Invariant m input Q emitted R) (MotifCoreStep.timeBound input.length) Q.coreCount hb

end JointThermoComplexity.Complexity.MotifCoreLoop

#print axioms JointThermoComplexity.Complexity.MotifCoreLoop.framed
