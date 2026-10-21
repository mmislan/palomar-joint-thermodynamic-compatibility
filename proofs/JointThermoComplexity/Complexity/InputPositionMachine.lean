module
public import proofs.JointThermoComplexity.Complexity.CountRewind
public import proofs.JointThermoComplexity.Complexity.VirtualCursor

set_option autoImplicit false
@[expose] public section

/-! Reverse input traversal appends one unary mark per original prefix position. -/

namespace JointThermoComplexity.Complexity.InputPositionMachine
open _root_.Complexity _root_.Complexity.TM HeaderAt
variable {w : ℕ}

def appendMark (idx : Fin w) (work : Fin w → Tape) : Fin w → Tape :=
  Function.update work idx ((work idx).writeAndMove Γ.one .right)

def action (idx : Fin w) (q : Option Bool) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Option Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 := match q with
  | some false => (some true, (fun j => readBackWrite (sw j)), readBackWrite so,
      (if si = Γ.start then .right else .left), (fun j => idleDir (sw j)), idleDir so)
  | some true =>
      if si = Γ.start then (none, (fun j => readBackWrite (sw j)), readBackWrite so,
        .right, (fun j => idleDir (sw j)), idleDir so)
      else (some true, (fun j => if j = idx then .one else readBackWrite (sw j)), readBackWrite so,
        .left, (fun j => if j = idx then .right else idleDir (sw j)), idleDir so)
  | none => allReadBack none si sw so

def machine (idx : Fin w) : TM w where
  Q := Option Bool
  qstart := some false
  qhalt := none
  δ := action idx
  δ_right_of_start q si sw so := by
    cases q with
    | none => exact rightOfStart_allReadBack si sw so
    | some b =>
      cases b with
      | false => exact ⟨fun h => by simp [h], fun _ h => idleDir_right_of_start h, idleDir_right_of_start⟩
      | true =>
        dsimp only [action]
        split
        · exact ⟨fun _ => rfl, fun _ h => idleDir_right_of_start h, idleDir_right_of_start⟩
        · refine ⟨fun h => by contradiction, ?_, idleDir_right_of_start⟩
          intro j hj
          by_cases he : j = idx
          · simp only [he, ↓reduceIte]
          · simpa only [he, ↓reduceIte] using idleDir_right_of_start hj

theorem initial_step (idx : Fin w) (c : Cfg w (machine idx).Q) (hs : c.state = some false)
    (hi : c.input.read ≠ Γ.start) (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine idx).step c = some ⟨some true, c.input.move .left, c.work, c.output⟩ := by
  simp only [TM.step, machine, hs, Option.some_ne_none, ↓reduceIte, action, hi]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · exact funext (fun j => transitionTape_eq_self (hw j))
  · exact transitionTape_eq_self ho

theorem scan_step (idx : Fin w) (c : Cfg w (machine idx).Q) (hs : c.state = some true)
    (hi : c.input.read ≠ Γ.start) (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine idx).step c = some ⟨some true, c.input.move .left, appendMark idx c.work, c.output⟩ := by
  simp only [TM.step, machine, hs, Option.some_ne_none, ↓reduceIte, action, hi]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    by_cases hj : j = idx
    · subst j
      simp only [appendMark, Function.update_self, ↓reduceIte]
      rfl
    · simp only [appendMark, Function.update_of_ne hj, hj, ↓reduceIte]
      exact transitionTape_eq_self (hw j)
  · exact transitionTape_eq_self ho

theorem finish_step (idx : Fin w) (c : Cfg w (machine idx).Q) (hs : c.state = some true)
    (hi : c.input.read = Γ.start) (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine idx).step c = some ⟨none, c.input.move .right, c.work, c.output⟩ := by
  simp only [TM.step, machine, hs, Option.some_ne_none, ↓reduceIte, action, hi]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · rfl
  · exact funext (fun j => transitionTape_eq_self (hw j))
  · exact transitionTape_eq_self ho

theorem append_prefix (idx : Fin w) (work : Fin w → Tape) (v : ℕ)
    (hp : (work idx).HasBinaryPrefix (List.replicate v true)) :
    (appendMark idx work idx).HasBinaryPrefix (List.replicate (v + 1) true) := by
  simpa only [appendMark, Function.update_self, List.replicate_add, List.replicate_one, Γ.ofBool] using
    Tape.hasBinaryPrefix_write_bit true hp

theorem append_zero (idx : Fin w) (work : Fin w → Tape) (v : ℕ)
    (hp : (work idx).HasBinaryPrefix (List.replicate v true)) (hz : (work idx).cells 0 = Γ.start) :
    (appendMark idx work idx).cells 0 = Γ.start := by
  simpa only [appendMark, Function.update_self, Γ.ofBool] using Tape.hasBinaryPrefix_write_bit_cell0 true hp hz

end JointThermoComplexity.Complexity.InputPositionMachine

#print axioms JointThermoComplexity.Complexity.InputPositionMachine.scan_step
#print axioms JointThermoComplexity.Complexity.InputPositionMachine.append_prefix
