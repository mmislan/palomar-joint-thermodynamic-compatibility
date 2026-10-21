module
public import proofs.JointThermoComplexity.Complexity.BinaryDifferenceResult

set_option autoImplicit false
@[expose] public section

/-! The real borrow-scan machine halts after the maximum operand width plus one step. -/

namespace JointThermoComplexity.Complexity.BinaryDifferenceScan
open _root_.Complexity
open _root_.Complexity.TM
open BinaryBorrow BinaryDifferenceMachine BinaryDifferenceCursor BinaryDifferenceResult

variable {w : ℕ}

theorem run (left right flag : Fin w) (sep : Separate left right flag) (emit carry : Bool)
    (px py xs ys emitted : List Bool) (c : Cfg w (Option Bool))
    (hs : c.state = some carry) (hc : Ready left right flag px py xs ys emitted c) :
    ∃ d, (machine left right flag emit).reachesIn (max xs.length ys.length + 1) c d ∧
      (machine left right flag emit).halted d ∧ Result left right flag emit carry px py xs ys emitted c d := by
  by_cases he : xs = [] ∧ ys = []
  · rcases he with ⟨rfl, rfl⟩
    exact ⟨finishCfg flag emit carry c, reachesIn.step (finish_step left right flag emit carry px py emitted c hs hc) reachesIn.zero,
      rfl, finish_result left right flag sep emit carry px py emitted c hc⟩
  · obtain ⟨d, hd, hh, hr⟩ := run left right flag sep emit
      (borrow (xs.head?.getD false) (ys.head?.getD false) carry)
      (px ++ consumed xs) (py ++ consumed ys) xs.tail ys.tail (nextEmitted emit carry xs ys emitted)
      (nextCfg left right emit carry xs ys c) rfl (next_ready left right flag sep emit carry px py xs ys emitted c hc)
    refine ⟨d, ?_, hh, lift_result left right flag sep emit carry px py xs ys emitted c d hc he hr⟩
    rw [← tail_width xs ys he]
    exact reachesIn.step (next_step left right flag emit carry px py xs ys emitted c hs hc he) hd
termination_by max xs.length ys.length
decreasing_by
  have hwidth := tail_width xs ys he
  omega

end JointThermoComplexity.Complexity.BinaryDifferenceScan

#print axioms JointThermoComplexity.Complexity.BinaryDifferenceScan.run
