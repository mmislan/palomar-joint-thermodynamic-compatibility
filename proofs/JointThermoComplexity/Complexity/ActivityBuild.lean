module
public import proofs.JointThermoComplexity.Complexity.ActivityLoopEntry
public import proofs.JointThermoComplexity.Complexity.ActivityCode

set_option autoImplicit false
@[expose] public section

/-! Emit the exact complete allFin positivity formula using the retained species count and canonical truth terminator. -/

namespace JointThermoComplexity.Complexity.ActivityBuild
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts MonomialPorts ActivityState CurrentTraversal

def machine (m : ℕ) : TM (m + 15) :=
  seqTM (ActivityLoop.machine m (MonomialFuel.slot (m + 1))) (emitBitsTM [false, false, false])

def timeBound (L : ℕ) : ℕ := 32 * L ^ 3 + 56 * L ^ 2 + 43 * L + 6

theorem hoareTime {n arity : ℕ} (m L : ℕ) (ha : arity ≤ 4 * L) (hn : n ≤ L)
    (indices : Fin n → Fin arity) (hindices : ∀ i, (indices i).val = i.val)
    (before input emitted : List Bool) (R : (Fin (m + 15) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ species (m + 1) → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ Ready m 0 R work ∧
        IsReg n (work (MonomialFuel.slot (m + 1))))
      (fun inp work out => Cursor before input (emitted ++ (ActivityCode.formula indices).code) inp work out ∧ Ready m n R work ∧
        IsReg n (work (MonomialFuel.slot (m + 1)))) (timeBound L) := by
  have hl := ActivityLoopEntry.hoareTime m L ha hn (MonomialFuel.slot (m + 1))
    (MonomialFuel.slot_separate (m + 1)).species (MonomialFuel.slot_separate (m + 1)).scratch
    indices hindices (ActivityCode.clauses indices) (ActivityCode.clauses_length indices) (ActivityCode.clause_at indices)
    before input emitted R hR
  have ht := FixedOutput.hoareTime [false, false, false] before input
    (emitted ++ output (ActivityCode.clauses indices)) (fun work => Ready m n R work ∧
      IsReg n (work (MonomialFuel.slot (m + 1))))
  have hseq := seqTM_hoareTime (ActivityLoop.machine m (MonomialFuel.slot (m + 1))) (emitBitsTM [false, false, false]) hl (by
    rintro inp work out ⟨hc, hr, hf⟩
    obtain ⟨hi, hw, ho⟩ := hc.phase
    rw [hi, hw, ho]
    exact ⟨hc, hr.1, hr, hf⟩) ht
  exact hseq.consequence (fun _ _ _ hp => hp) (by
    rintro inp work out ⟨hc, _, hr, hf⟩
    refine ⟨?_, hr, hf⟩
    rw [← ActivityCode.output_eq]
    simpa only [List.append_assoc] using hc) (by
      unfold timeBound ActivityLoopEntry.timeBound
      simp only [List.length_cons, List.length_nil]
      omega)

end JointThermoComplexity.Complexity.ActivityBuild

#print axioms JointThermoComplexity.Complexity.ActivityBuild.hoareTime
