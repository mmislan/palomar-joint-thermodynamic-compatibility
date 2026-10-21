module
public import proofs.JointThermoComplexity.Complexity.PayloadLoopMachine
public import proofs.JointThermoComplexity.Complexity.InputCursor

set_option autoImplicit false
@[expose] public section

/-! Exact entry, delimiter and loopback transitions of the actual encoded-payload controller. -/

namespace JointThermoComplexity.Complexity.PayloadLoopSteps
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt PayloadLoopMachine

variable {w : ℕ}

theorem test_one (body : TM w) (before tail emitted : List Bool) (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before (true :: tail) emitted inp work out) :
    (PayloadLoopMachine.machine body).step ⟨(PayloadLoopMachine.machine body).qstart, inp, work, out⟩ =
      some (wrap body ⟨body.qstart, inp.move .right, work, out⟩) := by
  have hi := InputCursor.read_bit true hc
  simp only [TM.step, PayloadLoopMachine.machine, hi, advance]
  change some (⟨.inr body.qstart, inp.move .right, (fun j => transitionTape (work j)), transitionTape out⟩ :
    Cfg w (Bool ⊕ body.Q)) = _
  rw [funext (fun j => transitionTape_eq_self (hc.works j).1), transitionTape_eq_self hc.output_read]
  rfl

theorem test_zero (body : TM w) (before tail emitted : List Bool) (inp : Tape) (work : Fin w → Tape) (out : Tape)
    (hc : Cursor before (false :: tail) emitted inp work out) :
    (PayloadLoopMachine.machine body).step ⟨(PayloadLoopMachine.machine body).qstart, inp, work, out⟩ =
      some ⟨(PayloadLoopMachine.machine body).qhalt, inp.move .right, work, out⟩ := by
  have hi := InputCursor.read_bit false hc
  simp only [TM.step, PayloadLoopMachine.machine, hi, advance]
  change some (⟨.inl true, inp.move .right, (fun j => transitionTape (work j)), transitionTape out⟩ :
    Cfg w (Bool ⊕ body.Q)) = _
  rw [funext (fun j => transitionTape_eq_self (hc.works j).1), transitionTape_eq_self hc.output_read]

theorem loopback (body : TM w) (before input emitted : List Bool) (c : Cfg w body.Q)
    (hh : body.halted c) (hc : Cursor before input emitted c.input c.work c.output) :
    (PayloadLoopMachine.machine body).step (wrap body c) = some ⟨(PayloadLoopMachine.machine body).qstart, c.input, c.work, c.output⟩ := by
  change c.state = body.qhalt at hh
  simp only [TM.step, PayloadLoopMachine.machine, wrap, hh, reduceCtorEq, ↓reduceIte, allReadBack]
  change some (⟨.inl false, transitionInput c.input, (fun j => transitionTape (c.work j)), transitionTape c.output⟩ :
    Cfg w (Bool ⊕ body.Q)) = _
  obtain ⟨hi, hw, ho⟩ := hc.phase
  rw [hi, hw, ho]

end JointThermoComplexity.Complexity.PayloadLoopSteps

#print axioms JointThermoComplexity.Complexity.PayloadLoopSteps.loopback
