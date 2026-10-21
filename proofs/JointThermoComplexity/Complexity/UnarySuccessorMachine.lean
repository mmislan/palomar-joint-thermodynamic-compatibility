module
public import proofs.JointThermoComplexity.Complexity.HeaderAt

set_option autoImplicit false
@[expose] public section

/-! Scan a bounded unary address and append one mark, leaving the real input and output unchanged. -/

namespace JointThermoComplexity.Complexity.UnarySuccessorMachine
open _root_.Complexity
open _root_.Complexity.TM

variable {w : ℕ}

def action (idx : Fin w) (next : Bool) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (next, (fun j => if j = idx then .one else readBackWrite (sw j)), readBackWrite so, idleDir si,
    (fun j => if j = idx then .right else idleDir (sw j)), idleDir so)

theorem action_right (idx : Fin w) (next : Bool) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    let (_, _, _, di, dw, dout) := action idx next si sw so
    (si = Γ.start → di = .right) ∧ (∀ j, sw j = Γ.start → dw j = .right) ∧ (so = Γ.start → dout = .right) := by
  refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
  intro j hj
  change (if j = idx then Dir3.right else idleDir (sw j)) = .right
  split
  · rfl
  · exact idleDir_right_of_start hj

def machine (idx : Fin w) : TM w where
  Q := Bool
  qstart := false
  qhalt := true
  δ q si sw so := match q, sw idx with
    | false, .one => action idx false si sw so
    | false, .blank => action idx true si sw so
    | _, _ => allReadBack true si sw so
  δ_right_of_start q si sw so := by
    cases q <;> cases h : sw idx <;> first
      | exact action_right idx false si sw so
      | exact action_right idx true si sw so
      | exact rightOfStart_allReadBack si sw so

theorem action_step (idx : Fin w) (next : Bool) (c : Cfg w (machine idx).Q)
    (hs : c.state = false)
    (hδ : (machine idx).δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      action idx next c.input.read (fun j => (c.work j).read) c.output.read)
    (hi : c.input.read ≠ Γ.start) (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine idx).step c = some ⟨next, c.input,
      Function.update c.work idx ((c.work idx).writeAndMove Γ.one .right), c.output⟩ := by
  rw [TM.step, ite_eq_right (by simp [machine, hs]), hδ]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · exact transitionInput_eq_self hi
  · funext j
    by_cases hj : j = idx
    · subst j
      simp
    · simpa [action, hj, transitionTape] using transitionTape_eq_self (hw j)
  · exact transitionTape_eq_self ho

theorem one_step (idx : Fin w) (v head : ℕ) (hh : 1 ≤ head) (hv : head ≤ v)
    (c : Cfg w (machine idx).Q) (hs : c.state = false) (ht : c.work idx = ⟨head, regCells v⟩)
    (hi : c.input.read ≠ Γ.start) (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine idx).step c = some ⟨false, c.input, Function.update c.work idx ⟨head + 1, regCells v⟩, c.output⟩ := by
  have hread : (c.work idx).read = Γ.one := by rw [ht]; exact regCells_one hh hv
  have hwrite : Function.update (regCells v) head Γ.one = regCells v := by
    rw [← regCells_one hh hv, Function.update_eq_self]
  have htape : (c.work idx).writeAndMove Γ.one .right = ⟨head + 1, regCells v⟩ := by
    rw [ht]
    simp only [Tape.writeAndMove, Tape.write, show ¬ head = 0 by omega, ↓reduceIte, Tape.move, hwrite]
  have h := action_step idx false c hs (by simp only [machine, hs, hread]) hi hw ho
  simpa only [htape] using h

theorem blank_step (idx : Fin w) (v : ℕ) (c : Cfg w (machine idx).Q)
    (hs : c.state = false) (ht : c.work idx = ⟨v + 1, regCells v⟩)
    (hi : c.input.read ≠ Γ.start) (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine idx).step c = some ⟨true, c.input, Function.update c.work idx ⟨v + 2, regCells (v + 1)⟩, c.output⟩ := by
  have hread : (c.work idx).read = Γ.blank := by rw [ht]; exact regCells_blank le_rfl
  have htape : (c.work idx).writeAndMove Γ.one .right = ⟨v + 2, regCells (v + 1)⟩ := by
    rw [ht]
    simp only [Tape.writeAndMove, Tape.write, Nat.add_one_ne_zero, ↓reduceIte, Tape.move, regCells_update_succ]
  have h := action_step idx true c hs (by simp only [machine, hs, hread]) hi hw ho
  simpa only [htape] using h

end JointThermoComplexity.Complexity.UnarySuccessorMachine

#print axioms JointThermoComplexity.Complexity.UnarySuccessorMachine.blank_step
