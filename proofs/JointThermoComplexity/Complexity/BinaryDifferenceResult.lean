module
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceCursor

set_option autoImplicit false
@[expose] public section

/-! Complete borrow-scan results compose exactly across one actual digit transition. -/

namespace JointThermoComplexity.Complexity.BinaryDifferenceResult
open _root_.Complexity
open _root_.Complexity.TM
open BinaryBorrow BinaryDifferenceMachine BinaryDifferenceStep BinaryDifferenceFrame BinaryDifferenceCursor

variable {w : ℕ}

structure Result (left right flag : Fin w) (emit carry : Bool) (px py xs ys emitted : List Bool)
    (c d : Cfg w (Option Bool)) : Prop where
  input_eq : d.input = c.input
  leftDone : Operand (px ++ xs) [] (d.work left)
  rightDone : Operand (py ++ ys) [] (d.work right)
  flag_tape : d.work flag = if emit then c.work flag else (c.work flag).write (Γ.ofBool (BinaryDifference.subtract xs ys carry).2)
  others : ∀ j, j ≠ left → j ≠ right → j ≠ flag → d.work j = c.work j
  safe : ∀ j, Parked (d.work j)
  outputPrefix : d.output.HasBinaryPrefix (emitted ++ (if emit then (BinaryDifference.subtract xs ys carry).1 else []))
  zero : d.output.cells 0 = Γ.start

def finishCfg (flag : Fin w) (emit carry : Bool) (c : Cfg w (Option Bool)) : Cfg w (Option Bool) :=
  ⟨none, transitionInput c.input, finishWork flag emit carry c.work, transitionTape c.output⟩

theorem finish_step (left right flag : Fin w) (emit carry : Bool) (px py emitted : List Bool)
    (c : Cfg w (Option Bool)) (hs : c.state = some carry) (hc : Ready left right flag px py [] [] emitted c) :
    (machine left right flag emit).step c = some (finishCfg flag emit carry c) :=
  end_step left right flag emit carry c hs hc.left.read hc.right.read

theorem finish_result (left right flag : Fin w) (sep : Separate left right flag) (emit carry : Bool)
    (px py emitted : List Bool) (c : Cfg w (Option Bool)) (hc : Ready left right flag px py [] [] emitted c) :
    Result left right flag emit carry px py [] [] emitted c (finishCfg flag emit carry c) := by
  have hl : (finishCfg flag emit carry c).work left = c.work left :=
    finish_other flag left emit carry c.work sep.flagLeft.symm (hc.safe left).read_ne_start
  have hr : (finishCfg flag emit carry c).work right = c.work right :=
    finish_other flag right emit carry c.work sep.flagRight.symm (hc.safe right).read_ne_start
  have ho : transitionTape c.output = c.output := transitionTape_eq_self (by simp [hc.outputPrefix.read_blank])
  refine ⟨transitionInput_eq_self hc.inputRead, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hl, List.append_nil] using hc.left
  · simpa only [hr, List.append_nil] using hc.right
  · cases emit
    · simpa only [finishCfg, Bool.false_eq_true, ↓reduceIte, BinaryDifference.subtract] using
        finish_compare flag carry c.work (hc.safe flag).read_ne_start
    · simpa only [finishCfg, ↓reduceIte] using congrFun (finish_emit flag carry c.work (fun j => (hc.safe j).read_ne_start)) flag
  · intro j _ _ hj
    exact finish_other flag j emit carry c.work hj (hc.safe j).read_ne_start
  · cases emit
    · exact finish_compare_parked flag carry c.work hc.safe
    · simpa only [finishCfg, finish_emit flag carry c.work (fun j => (hc.safe j).read_ne_start)] using hc.safe
  · simpa [finishCfg, ho, BinaryDifference.subtract] using hc.outputPrefix
  · simpa only [finishCfg, ho] using hc.zero

theorem lift_result (left right flag : Fin w) (sep : Separate left right flag) (emit carry : Bool)
    (px py xs ys emitted : List Bool) (c d : Cfg w (Option Bool)) (hc : Ready left right flag px py xs ys emitted c)
    (hne : ¬(xs = [] ∧ ys = []))
    (hres : Result left right flag emit (borrow (xs.head?.getD false) (ys.head?.getD false) carry)
      (px ++ consumed xs) (py ++ consumed ys) xs.tail ys.tail (nextEmitted emit carry xs ys emitted)
      (nextCfg left right emit carry xs ys c) d) :
    Result left right flag emit carry px py xs ys emitted c d := by
  have hpx : (px ++ consumed xs) ++ xs.tail = px ++ xs := by rw [List.append_assoc, consumed_tail]
  have hpy : (py ++ consumed ys) ++ ys.tail = py ++ ys := by rw [List.append_assoc, consumed_tail]
  have hstep := subtract_step xs ys carry hne
  have hsnd : (BinaryDifference.subtract xs.tail ys.tail (borrow (xs.head?.getD false) (ys.head?.getD false) carry)).2 =
      (BinaryDifference.subtract xs ys carry).2 := (congrArg Prod.snd hstep).symm
  have hflag := next_other left right flag emit carry px py xs ys emitted c hc flag sep.flagLeft sep.flagRight
  refine ⟨hres.input_eq.trans (next_input left right flag emit carry px py xs ys emitted c hc),
    by simpa only [hpx] using hres.leftDone, by simpa only [hpy] using hres.rightDone,
    by simpa only [hflag, hsnd] using hres.flag_tape, ?_, hres.safe, ?_, hres.zero⟩
  · intro j hl hr hf
    exact (hres.others j hl hr hf).trans (next_other left right flag emit carry px py xs ys emitted c hc j hl hr)
  · cases emit
    · simpa only [nextEmitted, Bool.false_eq_true, ↓reduceIte, List.append_nil] using hres.outputPrefix
    · simpa only [nextEmitted, ↓reduceIte, List.append_assoc, List.singleton_append, hstep] using hres.outputPrefix

end JointThermoComplexity.Complexity.BinaryDifferenceResult

#print axioms JointThermoComplexity.Complexity.BinaryDifferenceResult.finish_result
#print axioms JointThermoComplexity.Complexity.BinaryDifferenceResult.lift_result
