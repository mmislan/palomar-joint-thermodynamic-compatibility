module
public import proofs.JointThermoComplexity.Complexity.MotifCoreLoop
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! Canonical copied-core count entry/exit and a sixth-degree actual runtime bound. -/

namespace JointThermoComplexity.Complexity.MotifCoreLoopEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt MotifCoreState MotifCoreFuelFrame InvariantLoop CurrentTraversal

def timeBound (L : ℕ) : ℕ := 4 * L ^ 6 + 52 * L ^ 5 + 184 * L ^ 4 + 252 * L ^ 3 + 192 * L ^ 2 + 117 * L + 2

theorem runtime_bound (L c : ℕ) (hc : c ≤ L) : MotifCoreLoop.timeBound L c ≤ timeBound L := by
  unfold MotifCoreLoop.timeBound
  calc c * (MotifCoreStep.timeBound L + 2) + (c + 2) ≤ L * (MotifCoreStep.timeBound L + 2) + (L + 2) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hc) (Nat.add_le_add_right hc 2)
      _ = _ := by unfold MotifCoreStep.timeBound timeBound; ring1

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', MotifCompleteFrame.Unchanged m work work' → R work → R work') :
    (MotifCoreLoop.machine m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ State m input Q 0 R work ∧
        IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) ∧ IsReg Q.coreCount (work (fuel m)))
      (fun inp work out => Cursor [] input (emitted ++ output (MotifCoreDenseCode.clauses Q)) inp work out ∧
        State m input Q Q.coreCount R work ∧ IsReg Q.speciesCount (work (OuterFuelPorts.destination m 0)) ∧
        IsReg Q.coreCount (work (fuel m))) (timeBound input.length) := by
  have hf := MotifCoreLoop.framed m input Q hd emitted R hR
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  exact hf.consequence (by
    rintro inp work out ⟨hc, hp, hspecies, hcore⟩
    refine ⟨hcore.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work (fuel m) Q.coreCount hcore.eq_regT]
    simpa only [MotifCoreLoop.Invariant, List.take_zero, output, List.flatMap_nil, List.append_nil]
      using And.intro hc (And.intro hp hspecies)) (by
        intro inp work out hp
        have hclauses : (MotifCoreDenseCode.clauses Q).take Q.coreCount = MotifCoreDenseCode.clauses Q := by
          rw [← MotifCoreDenseCode.clauses_length Q, List.take_length]
        exact ⟨by simpa only [MotifCoreLoop.Invariant, hclauses] using hp.on_work.1,
          hp.on_work.2.1, hp.on_work.2.2, hp.register⟩) (runtime_bound input.length Q.coreCount (by omega))

end JointThermoComplexity.Complexity.MotifCoreLoopEntry

#print axioms JointThermoComplexity.Complexity.MotifCoreLoopEntry.runtime_bound
#print axioms JointThermoComplexity.Complexity.MotifCoreLoopEntry.hoareTime
