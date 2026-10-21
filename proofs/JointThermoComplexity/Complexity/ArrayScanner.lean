module
public import proofs.JointThermoComplexity.Complexity.ScannerSpec
public import proofs.JointThermoComplexity.Complexity.NaturalArray

set_option autoImplicit false
@[expose] public section

/-!
# Strong framed array specifications

After an array loop exits, its fuel register is exactly the initial canonical
register. This exposes the same two-status-tape frame as scalar scanners, even
for predicates that inspect the fuel tape itself.
-/

namespace JointThermoComplexity.Complexity.ArrayScanner
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt ScannerSpec

variable {n : ℕ}

theorem bound_mono (v : ℕ) : Monotone (fun L => v * (L + 6) + (v + 2)) := by
  intro a b h
  exact Nat.add_le_add_right (Nat.mul_le_mul_left v (Nat.add_le_add_right h 6)) (v + 2)

theorem natural_runs (requirePositive : Bool) (r master : Fin (n + 1))
    (hr : r ≠ NaturalMachine.flagIndex n) (hm : master ≠ NaturalMachine.flagIndex n) (hrm : r ≠ master) (v : ℕ) :
    Runs (RecordControl.array (NaturalArray.control requirePositive) v)
      (NaturalArray.machine requirePositive r master) master (NaturalMachine.flagIndex n)
      (fun work => IsReg v (work r)) (fun L => v * (L + 6) + (v + 2)) := by
  intro initial before input emitted R hR inp work out hpre
  rcases hpre with ⟨hc, hf, hmh, hmr, hreg, hstate⟩
  let RN : (Fin (n + 1) → Tape) → Prop := fun w => R (InvariantLoop.restore w r v)
  have hRN : ∀ w w',
      (∀ j, j ≠ r → j ≠ master → j ≠ NaturalMachine.flagIndex n → w' j = w j) → RN w → RN w' := by
    intro w w' h hr'
    apply hR (InvariantLoop.restore w r v) (InvariantLoop.restore w' r v) ?_ hr'
    intro j hjm hjf
    by_cases hj : j = r
    · subst j
      simp only [InvariantLoop.restore, Function.update_self]
    · rw [InvariantLoop.restore, Function.update_of_ne hj, InvariantLoop.restore, Function.update_of_ne hj]
      exact h j hj hjm hjf
  have hstate₀ : NaturalArray.StateInv requirePositive initial master before input emitted RN 0 inp work out := by
    apply (NaturalArray.start_iff requirePositive initial master before input emitted RN inp work out).mpr
    refine ⟨hc, hf, hmh, hmr, ?_⟩
    simpa only [RN, InvariantLoop.restore_self work r v hreg.eq_regT] using hstate
  obtain ⟨d, t, ht, hreach, hhalt, hreg', hcur, hf', hmh', hmr', hstate'⟩ :=
    NaturalArray.hoareTime requirePositive initial r master hr hm hrm v before input emitted RN hRN
      inp work out ⟨hreg, hstate₀⟩
  have hfinal : R d.work := by
    simpa only [RN, InvariantLoop.restore_self d.work r v hreg'.eq_regT] using hstate'
  exact ⟨d, t, ht, hreach, hhalt, hcur, hf', hmh', hmr', hreg', hfinal⟩

end JointThermoComplexity.Complexity.ArrayScanner

#print axioms JointThermoComplexity.Complexity.ArrayScanner.natural_runs
