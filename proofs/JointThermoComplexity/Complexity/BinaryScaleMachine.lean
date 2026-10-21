module
public import proofs.JointThermoComplexity.Complexity.BinaryScaleCanonical
public import proofs.JointThermoComplexity.Complexity.BinaryEmitMachine

set_option autoImplicit false
@[expose] public section

/-! A finite-carry binary multiplier. Each multiplier k has only two families
of k+1 carry states and a halt state; no magnitude-indexed control table. -/

namespace JointThermoComplexity.Complexity.BinaryScaleMachine
open _root_.Complexity _root_.Complexity.TM BinaryScaleControl
variable {w k : ℕ}

inductive State (k : ℕ) where
  | scan : Fin (k + 1) → State k
  | flush : Fin (k + 1) → State k
  | done
  deriving DecidableEq

instance : Fintype (State k) where
  elems := {State.done} ∪ Finset.univ.image State.scan ∪ Finset.univ.image State.flush
  complete q := by cases q <;> simp

def nextCarry (carry : Fin (k + 1)) (b : Bool) : Fin (k + 1) :=
  ⟨next k carry.val b, by have h := next_le k carry.val b (by omega); omega⟩

def half (carry : Fin (k + 1)) : Fin (k + 1) :=
  ⟨carry.val / 2, (Nat.div_le_self _ _).trans_lt carry.isLt⟩

def outputAction (idx : Fin w) (q : State k) (b advance : Bool) (si : Γ) (sw : Fin w → Γ) :
    State k × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (q, fun j => readBackWrite (sw j), Γw.ofBool b, idleDir si,
    fun j => if advance && decide (j = idx) then .right else idleDir (sw j), .right)

def action (idx : Fin w) (q : State k) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    State k × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  match q with
  | .scan carry =>
    match sw idx with
    | .zero => outputAction idx (.scan (nextCarry carry false)) (digit k carry.val false) true si sw
    | .one => outputAction idx (.scan (nextCarry carry true)) (digit k carry.val true) true si sw
    | .blank => allReadBack (.flush carry) si sw so
    | .start => allReadBack .done si sw so
  | .flush carry =>
    if carry.val = 0 then allReadBack .done si sw so
    else outputAction idx (.flush (half carry)) (decide (carry.val % 2 = 1)) false si sw
  | .done => allReadBack .done si sw so

def machine (k : ℕ) (idx : Fin w) : TM w where
  Q := State k
  qstart := .scan 0
  qhalt := .done
  δ := action idx
  δ_right_of_start q si sw so := by
    cases q with
    | scan carry =>
      cases h : sw idx <;> simp [action, h, outputAction, allReadBack, idleDir]
      all_goals intro j hj _; exact hj
    | flush carry =>
      by_cases hc : carry.val = 0 <;> simp [action, hc, allReadBack, outputAction, idleDir]
    | done => exact rightOfStart_allReadBack si sw so

theorem bit_step (idx : Fin w) (carry : Fin (k + 1)) (c : Cfg w (State k)) (b : Bool)
    (hs : c.state = .scan carry) (hr : (c.work idx).read = Γ.ofBool b) :
    (machine k idx).step c = some ⟨.scan (nextCarry carry b), transitionInput c.input,
      BinaryEmitMachine.readWork idx c.work, c.output.writeAndMove (Γ.ofBool (digit k carry.val b)) .right⟩ := by
  cases b with
  | false =>
    cases hd : digit k carry.val false <;>
      simp [TM.step, machine, action, outputAction, hs, hr, hd, BinaryEmitMachine.readWork,
        transitionInput, transitionTape, Γw.ofBool, Γ.ofBool, funext_iff]
    all_goals intro j; by_cases hj : j = idx <;> simp [hj]
  | true =>
    cases hd : digit k carry.val true <;>
      simp [TM.step, machine, action, outputAction, hs, hr, hd, BinaryEmitMachine.readWork,
        transitionInput, transitionTape, Γw.ofBool, Γ.ofBool, funext_iff]
    all_goals intro j; by_cases hj : j = idx <;> simp [hj]

theorem end_step (idx : Fin w) (carry : Fin (k + 1)) (c : Cfg w (State k))
    (hs : c.state = .scan carry) (hr : (c.work idx).read = Γ.blank) :
    (machine k idx).step c = some ⟨.flush carry, transitionInput c.input,
      (fun j => transitionTape (c.work j)), transitionTape c.output⟩ := by
  simp [TM.step, machine, action, hs, hr, allReadBack, transitionInput, transitionTape]

theorem flush_zero_step (idx : Fin w) (carry : Fin (k + 1)) (c : Cfg w (State k))
    (hs : c.state = .flush carry) (hz : carry.val = 0) :
    (machine k idx).step c = some ⟨.done, transitionInput c.input,
      (fun j => transitionTape (c.work j)), transitionTape c.output⟩ := by
  simp [TM.step, machine, action, hs, hz, allReadBack, transitionInput, transitionTape]

theorem flush_bit_step (idx : Fin w) (carry : Fin (k + 1)) (c : Cfg w (State k))
    (hs : c.state = .flush carry) (hz : carry.val ≠ 0) :
    (machine k idx).step c = some ⟨.flush (half carry), transitionInput c.input,
      (fun j => transitionTape (c.work j)),
      c.output.writeAndMove (Γ.ofBool (decide (carry.val % 2 = 1))) .right⟩ := by
  cases hb : decide (carry.val % 2 = 1) <;>
    simp [TM.step, machine, action, outputAction, hs, hz, hb, transitionInput, transitionTape, Γw.ofBool, Γ.ofBool]

end JointThermoComplexity.Complexity.BinaryScaleMachine

#print axioms JointThermoComplexity.Complexity.BinaryScaleMachine.machine
#print axioms JointThermoComplexity.Complexity.BinaryScaleMachine.bit_step
#print axioms JointThermoComplexity.Complexity.BinaryScaleMachine.flush_bit_step
