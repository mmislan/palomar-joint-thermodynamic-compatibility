module
public import proofs.JointThermoComplexity.Complexity.ProductionSpeciesLoop
public import Mathlib.Tactic.Ring.Basic

set_option autoImplicit false
@[expose] public section

/-! Canonical copied-species count entry/exit and a quintic bound for the actual complete loop. -/

namespace JointThermoComplexity.Complexity.ProductionSpeciesLoopEntry
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ProductionSpeciesState ProductionSpeciesFuelFrame InvariantLoop CurrentTraversal

def timeBound (L : ℕ) : ℕ := 4 * L ^ 5 + 52 * L ^ 4 + 150 * L ^ 3 + 184 * L ^ 2 + 65 * L + 2

theorem runtime_bound (L n : ℕ) (hn : n ≤ L) : ProductionSpeciesLoop.timeBound L n ≤ timeBound L := by
  unfold ProductionSpeciesLoop.timeBound
  calc n * (ProductionSpeciesStep.timeBound L + 2) + (n + 2) ≤
      L * (ProductionSpeciesStep.timeBound L + 2) + (L + 2) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hn) (Nat.add_le_add_right hn 2)
      _ = _ := by unfold ProductionSpeciesStep.timeBound timeBound; ring1

theorem hoareTime (m : ℕ) (input : List Bool) (Q : NetworkCodec.Input) (hd : NetworkCodec.decode input = some Q)
    (a : Fin Q.coreCount) (emitted : List Bool) (R : (Fin (m + 22) → Tape) → Prop)
    (hR : ∀ work work', ProductionSpeciesFrame.Unchanged m work work' → R work → R work') :
    (ProductionSpeciesLoop.machine m).HoareTime
      (fun inp work out => Cursor [] input emitted inp work out ∧ State m input Q a 0 R work ∧ IsReg Q.speciesCount (work (fuel m)))
      (fun inp work out => Cursor [] input (emitted ++ output (ProductionSpeciesDenseCode.clauses Q a)) inp work out ∧
        State m input Q a Q.speciesCount R work ∧ IsReg Q.speciesCount (work (fuel m))) (timeBound input.length) := by
  have hf := ProductionSpeciesLoop.framed m input Q hd a emitted R hR
  have hdims := NetworkCodec.decoded_dimensions_le_length hd
  exact hf.consequence (by
    rintro inp work out ⟨hc, hp, hr⟩
    refine ⟨hr.eq_regT, hc.input_read, (fun j _ => (hc.works j).1), hc.output_read, ?_⟩
    rw [restore_self work (fuel m) Q.speciesCount hr.eq_regT]
    simpa only [ProductionSpeciesLoop.Invariant, List.take_zero, output, List.flatMap_nil, List.append_nil]
      using And.intro hc hp) (by
        intro inp work out hp
        have hclauses : (ProductionSpeciesDenseCode.clauses Q a).take Q.speciesCount = ProductionSpeciesDenseCode.clauses Q a := by
          rw [← ProductionSpeciesDenseCode.clauses_length Q a, List.take_length]
        exact ⟨by simpa only [ProductionSpeciesLoop.Invariant, hclauses] using hp.on_work.1,
          hp.on_work.2, hp.register⟩) (runtime_bound input.length Q.speciesCount (by omega))

end JointThermoComplexity.Complexity.ProductionSpeciesLoopEntry

#print axioms JointThermoComplexity.Complexity.ProductionSpeciesLoopEntry.runtime_bound
#print axioms JointThermoComplexity.Complexity.ProductionSpeciesLoopEntry.hoareTime
