module
public import proofs.JointThermoComplexity.Complexity.PowerBitState
public import proofs.JointThermoComplexity.Complexity.FlagBranchRun

set_option autoImplicit false
@[expose] public section

/-! A uniform actual work-flag dispatch into the checked false/true power blocks. -/

namespace JointThermoComplexity.Complexity.PowerBitDispatch
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PowerPorts PowerBitState

variable {arity : ℕ}

def machine (m : ℕ) : TM (m + 13) :=
  FlagBranch.machine (PowerBitState.flag m) (PowerTrueBlock.machine m) (PowerFalseBlock.machine m)

theorem hoareTime (m : ℕ) (values : Fin (m + 13) → Fin arity) (bit : Bool)
    (room : bit = true → (values (next m)).val + 1 < arity) (L : ℕ) (ha : arity ≤ 4 * L)
    (before input emitted : List Bool) (R : (Fin (m + 13) → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ next m → j ≠ accumulator m → j ≠ power m → work' j = work j) → R work → R work') :
    (machine m).HoareTime
      (fun inp work out => (Cursor before input emitted inp work out ∧ Ready m values R work) ∧
        (work (PowerBitState.flag m)).read = Γ.ofBool bit)
      (fun inp work out => Cursor before input (emitted ++ word m values bit room) inp work out ∧ After m values bit R work)
      (bound L) := by
  cases bit with
  | false =>
    have hf := PowerFalseBlock.hoareTime m values before input emitted R hR
    have hf' : (PowerFalseBlock.machine m).HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ Ready m values R work)
        (fun inp work out => Cursor before input (emitted ++ PowerFalseBlock.word m values) inp work out ∧ After m values false R work)
        (PowerFalseBlock.timeBound m values) := by
      exact hf.consequence (fun _ _ _ h => h)
        (fun _ _ _ h => by simpa only [After, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.add_zero] using h) le_rfl
    have hb := FlagBranchRun.no_hoareTime (PowerBitState.flag m) (PowerTrueBlock.machine m) (PowerFalseBlock.machine m)
      before input emitted before input (emitted ++ PowerFalseBlock.word m values)
      (Ready m values R) (After m values false R) (PowerFalseBlock.timeBound m values) hf'
    exact hb.consequence (fun _ _ _ h => h)
      (fun _ _ _ h => by simpa only [word, Bool.false_eq_true, ↓reduceDIte] using h) (by
        have ht := PowerBlockRuntime.false_bound m values L ha
        unfold bound
        omega)
  | true =>
    have ht := PowerTrueBlock.hoareTime m values (room rfl) before input emitted R hR
    have ht' : (PowerTrueBlock.machine m).HoareTime
        (fun inp work out => Cursor before input emitted inp work out ∧ Ready m values R work)
        (fun inp work out => Cursor before input (emitted ++ PowerTrueBlock.word m values (room rfl)) inp work out ∧ After m values true R work)
        (PowerTrueBlock.timeBound m values (room rfl)) := by
      exact ht.consequence (fun _ _ _ h => h)
        (fun _ _ _ h => by simpa only [After, ↓reduceIte, Bool.toNat_true] using h) le_rfl
    have hb := FlagBranchRun.yes_hoareTime (PowerBitState.flag m) (PowerTrueBlock.machine m) (PowerFalseBlock.machine m)
      before input emitted before input (emitted ++ PowerTrueBlock.word m values (room rfl))
      (Ready m values R) (After m values true R) (PowerTrueBlock.timeBound m values (room rfl)) ht'
    exact hb.consequence (fun _ _ _ h => h)
      (fun _ _ _ h => by simpa only [word, ↓reduceDIte] using h) (by
        have ht := PowerBlockRuntime.true_bound m values (room rfl) L ha
        unfold bound
        omega)

end JointThermoComplexity.Complexity.PowerBitDispatch

#print axioms JointThermoComplexity.Complexity.PowerBitDispatch.hoareTime
