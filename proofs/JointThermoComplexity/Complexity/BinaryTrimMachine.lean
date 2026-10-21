module
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Move left from a raw binary end, erase high zeros, then park immediately after the highest one. -/

namespace JointThermoComplexity.Complexity.BinaryTrimMachine
open _root_.Complexity
open _root_.Complexity.TM

variable {w : ℕ}

def workDir (idx : Fin w) (dir : Dir3) (sw : Fin w → Γ) (j : Fin w) : Dir3 :=
  if sw j = Γ.start then .right else if j = idx then dir else idleDir (sw j)

def updateAction (idx : Fin w) (q : Option Bool) (erase : Bool) (dir : Dir3)
    (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Option Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (q, fun j => if j = idx ∧ erase = true then .blank else readBackWrite (sw j), readBackWrite so,
    idleDir si, workDir idx dir sw, idleDir so)

def action (idx : Fin w) (q : Option Bool) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Option Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  match q with
  | none => allReadBack none si sw so
  | some false => updateAction idx (some true) false .left si sw so
  | some true => if sw idx = Γ.zero then updateAction idx (some true) true .left si sw so
      else updateAction idx none false .right si sw so

theorem update_right_of_start (idx : Fin w) (q : Option Bool) (erase : Bool) (dir : Dir3)
    (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    let (_, _, _, di, dw, dout) := updateAction idx q erase dir si sw so
    (si = Γ.start → di = .right) ∧ (∀ j, sw j = Γ.start → dw j = .right) ∧
      (so = Γ.start → dout = .right) := by
  refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
  intro j hj
  simp only [workDir, hj, ↓reduceIte]

def machine (idx : Fin w) : TM w where
  Q := Option Bool
  qstart := some false
  qhalt := none
  δ := action idx
  δ_right_of_start q si sw so := by
    cases q with
    | none => exact rightOfStart_allReadBack si sw so
    | some b =>
      cases b
      · exact update_right_of_start idx (some true) false .left si sw so
      · simp only [action]
        split
        · exact update_right_of_start idx (some true) true .left si sw so
        · exact update_right_of_start idx none false .right si sw so

def workUpdate (idx : Fin w) (erase : Bool) (dir : Dir3) (work : Fin w → Tape) : Fin w → Tape := fun j =>
  (work j).writeAndMove (if j = idx ∧ erase = true then (Γw.blank : Γ) else (readBackWrite (work j).read : Γ))
    (workDir idx dir (fun k => (work k).read) j)

def cfg (idx : Fin w) (q : Option Bool) (erase : Bool) (dir : Dir3) (c : Cfg w (Option Bool)) : Cfg w (Option Bool) :=
  ⟨q, transitionInput c.input, workUpdate idx erase dir c.work, transitionTape c.output⟩

theorem start_step (idx : Fin w) (c : Cfg w (Option Bool)) (hs : c.state = some false) :
    (machine idx).step c = some (cfg idx (some true) false .left c) := by
  simp [TM.step, machine, action, updateAction, cfg, hs, transitionInput, transitionTape]
  funext j
  unfold workUpdate
  by_cases hj : j = idx <;> simp [hj]

theorem erase_step (idx : Fin w) (c : Cfg w (Option Bool)) (hs : c.state = some true)
    (hr : (c.work idx).read = Γ.zero) :
    (machine idx).step c = some (cfg idx (some true) true .left c) := by
  simp [TM.step, machine, action, updateAction, cfg, hs, hr, transitionInput, transitionTape]
  funext j
  unfold workUpdate
  by_cases hj : j = idx <;> simp [hj]

theorem stop_step (idx : Fin w) (c : Cfg w (Option Bool)) (hs : c.state = some true)
    (hr : (c.work idx).read ≠ Γ.zero) :
    (machine idx).step c = some (cfg idx none false .right c) := by
  simp [TM.step, machine, action, updateAction, cfg, hs, hr, transitionInput, transitionTape]
  funext j
  unfold workUpdate
  by_cases hj : j = idx <;> simp [hj]

end JointThermoComplexity.Complexity.BinaryTrimMachine

#print axioms JointThermoComplexity.Complexity.BinaryTrimMachine.start_step
#print axioms JointThermoComplexity.Complexity.BinaryTrimMachine.erase_step
#print axioms JointThermoComplexity.Complexity.BinaryTrimMachine.stop_step
