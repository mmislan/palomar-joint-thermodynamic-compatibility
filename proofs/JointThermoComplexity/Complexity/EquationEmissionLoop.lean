module
public import proofs.JointThermoComplexity.Complexity.EquationLoopBody

set_option autoImplicit false
@[expose] public section

/-! A bounded actual loop emits the exact complete raw preorder row list and restores its fuel head. -/

namespace JointThermoComplexity.Complexity.EquationEmissionLoop
open _root_.Complexity _root_.Complexity.TM EquationFuelFrame EquationLoopBounds

def machine : TM 32 := forRegTM EquationEmissionStep.machine fuel
noncomputable def timeBound (L N : ℕ) : ℕ := L * (EquationEmissionStep.timeBound N + 2) + (L + 2)

theorem framed_hoareTime (arity L : ℕ) (s : PreorderEmissionControl.State) (hlen : s.scan.input.length ≤ L) :
    machine.HoareTime
      (InvariantLoop.Frame fuel L 1 (Logical s arity L (bound arity L s)))
      (InvariantLoop.Frame fuel L 1 (Logical (PreorderEmissionControl.run L arity L s) arity L (bound arity L s)))
      (timeBound L (bound arity L s)) :=
  InvariantLoop.hoareTime EquationEmissionStep.machine fuel
    (fun i => Logical (PreorderEmissionControl.run L arity i s) arity L (bound arity L s))
    (EquationEmissionStep.timeBound (bound arity L s)) L
    (fun i hi => EquationLoopBody.hoareTime arity L i s hi hlen)

theorem hoareTime (arity L : ℕ) (s : PreorderEmissionControl.State) (hlen : s.scan.input.length ≤ L) :
    machine.HoareTime
      (fun inp work out => Logical s arity L (bound arity L s) inp work out ∧ IsReg L (work fuel))
      (fun inp work out => Logical (PreorderEmissionControl.run L arity L s) arity L (bound arity L s) inp work out ∧ IsReg L (work fuel))
      (timeBound L (bound arity L s)) := by
  have h := framed_hoareTime arity L s hlen
  apply h.consequence
  · rintro inp work out ⟨hi, hf⟩
    refine ⟨hf.eq_regT, hi.1.input_read, fun j _ => (hi.1.works j).1, hi.1.output_read, ?_⟩
    simpa only [InvariantLoop.restore_self work fuel L hf.eq_regT] using hi
  · exact fun _ _ _ hf => ⟨hf.on_work, hf.register⟩
  · exact le_rfl

end JointThermoComplexity.Complexity.EquationEmissionLoop

#print axioms JointThermoComplexity.Complexity.EquationEmissionLoop.hoareTime
