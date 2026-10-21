module
public import proofs.JointThermoComplexity.Complexity.InputCursor

set_option autoImplicit false
@[expose] public section

/-! Count repeated-squaring gates directly while scanning encoded exponent bits. -/

namespace JointThermoComplexity.Complexity.GateTallyMachine
open _root_.Complexity
open _root_.Complexity.TM

variable {w : ℕ}

def action (idx : Fin w) (add : Bool) (next : Option Bool) (_si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Option Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (next, (fun j => if add = true ∧ j = idx then .one else readBackWrite (sw j)), readBackWrite so, .right,
    (fun j => if add = true ∧ j = idx then .right else idleDir (sw j)), idleDir so)

theorem action_right (idx : Fin w) (add : Bool) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    let (_, _, _, di, dw, dout) := action idx add none si sw so
    (si = Γ.start → di = .right) ∧ (∀ j, sw j = Γ.start → dw j = .right) ∧ (so = Γ.start → dout = .right) := by
  refine ⟨fun _ => rfl, ?_, idleDir_right_of_start⟩
  intro j hj
  change (if add = true ∧ j = idx then Dir3.right else idleDir (sw j)) = .right
  split
  · rfl
  · exact idleDir_right_of_start hj

def machine (idx : Fin w) : TM w where
  Q := Option Bool
  qstart := some false
  qhalt := none
  δ q si sw so := match q, si with
    | some false, .one => action idx true (some true) si sw so
    | some true, .one => action idx true (some false) si sw so
    | some false, .zero => action idx false none si sw so
    | some true, .zero => action idx false (some false) si sw so
    | _, _ => allReadBack none si sw so
  δ_right_of_start q si sw so := by
    cases q with
    | none => exact rightOfStart_allReadBack si sw so
    | some b =>
      cases b <;> cases si <;> first
        | exact action_right idx true _ sw so
        | exact action_right idx false _ sw so
        | exact rightOfStart_allReadBack _ sw so

def changedWork (idx : Fin w) (add : Bool) (work : Fin w → Tape) : Fin w → Tape :=
  if add then Function.update work idx ((work idx).writeAndMove Γ.one .right) else work

theorem action_step (idx : Fin w) (add : Bool) (next : Option Bool) (c : Cfg w (machine idx).Q)
    (hne : c.state ≠ none)
    (hδ : (machine idx).δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      action idx add next c.input.read (fun j => (c.work j).read) c.output.read)
    (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine idx).step c = some ⟨next, c.input.move .right, changedWork idx add c.work, c.output⟩ := by
  rw [TM.step, ite_eq_right (show c.state ≠ (machine idx).qhalt from hne), hδ]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    change (c.work j).writeAndMove
      ((if add = true ∧ j = idx then Γw.one else readBackWrite (c.work j).read).toΓ)
      (if add = true ∧ j = idx then .right else idleDir (c.work j).read) = changedWork idx add c.work j
    cases add with
    | false => simpa [changedWork, transitionTape] using transitionTape_eq_self (hw j)
    | true =>
      by_cases hj : j = idx
      · subst j
        simp [changedWork]
      · simpa [changedWork, transitionTape, hj] using transitionTape_eq_self (hw j)
  · exact transitionTape_eq_self ho

theorem one_step (idx : Fin w) (bitPhase : Bool) (c : Cfg w (machine idx).Q)
    (hs : c.state = some bitPhase) (hr : c.input.read = Γ.one)
    (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine idx).step c = some ⟨some (!bitPhase), c.input.move .right, changedWork idx true c.work, c.output⟩ := by
  apply action_step idx true (some (!bitPhase)) c (by simp [machine, hs]) ?_ hw ho
  cases bitPhase <;> simp [machine, hs, hr]

theorem zero_step (idx : Fin w) (bitPhase : Bool) (c : Cfg w (machine idx).Q)
    (hs : c.state = some bitPhase) (hr : c.input.read = Γ.zero)
    (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine idx).step c = some ⟨(if bitPhase then some false else none), c.input.move .right, c.work, c.output⟩ := by
  have ha := action_step idx false (if bitPhase then some false else none) c (by simp [machine, hs]) (by
    cases bitPhase <;> simp [machine, hs, hr]) hw ho
  simpa only [machine, changedWork, Bool.false_eq_true, ↓reduceIte] using ha

end JointThermoComplexity.Complexity.GateTallyMachine

#print axioms JointThermoComplexity.Complexity.GateTallyMachine.action_step
