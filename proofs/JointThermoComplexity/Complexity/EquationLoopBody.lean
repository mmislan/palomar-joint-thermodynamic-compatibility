module
public import proofs.JointThermoComplexity.Complexity.EquationLoopBounds

set_option autoImplicit false
@[expose] public section

/-! The actual emission body preserves the displaced fuel tape and advances the exact loop invariant. -/

namespace JointThermoComplexity.Complexity.EquationLoopBody
open _root_.Complexity _root_.Complexity.TM EquationFuelFrame EquationLoopBounds

theorem hoareTime (arity L i : ℕ) (s : PreorderEmissionControl.State) (hi : i < L) (hlen : s.scan.input.length ≤ L) :
    EquationEmissionStep.machine.HoareTime
      (InvariantLoop.Frame fuel L (i + 2) (Logical (PreorderEmissionControl.run L arity i s) arity L (bound arity L s)))
      (InvariantLoop.Frame fuel L (i + 2) (Logical (PreorderEmissionControl.run L arity (i + 1) s) arity L (bound arity L s)))
      (EquationEmissionStep.timeBound (bound arity L s)) := by
  let q := PreorderEmissionControl.run L arity i s
  let N := bound arity L s
  obtain ⟨ha, hL, ht, hf, hc, hp, hinput⟩ := current_bounds arity L i s (by omega) hlen
  have hb := EquationEmissionStep.hoareTime q arity L N ha hL ht hf hc hp hinput
    (ExactFuel L (i + 2)) (exact_stable L (i + 2))
  intro inp work out hframe
  have hpre := to_actual q arity L N L (i + 2) (by omega) inp work out hframe
  obtain ⟨d, t, htime, hd, hh, hcur, hr⟩ := hb inp work out hpre
  have hpost := from_actual (PreorderEmissionControl.step L arity q) arity L N L (i + 2) d.input d.work d.output hcur hr
  refine ⟨d, t, htime, hd, hh, ?_⟩
  simpa only [run_succ_last] using hpost

end JointThermoComplexity.Complexity.EquationLoopBody

#print axioms JointThermoComplexity.Complexity.EquationLoopBody.hoareTime
