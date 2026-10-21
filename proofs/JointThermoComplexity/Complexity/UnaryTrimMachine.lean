module
public import proofs.JointThermoComplexity.Complexity.CountTape

set_option autoImplicit false
@[expose] public section

/-! Two actual transitions remove the final mark of a nonempty unary prefix at its end cursor. -/

namespace JointThermoComplexity.Complexity.UnaryTrimMachine
open _root_.Complexity
open _root_.Complexity.TM

variable {w : ℕ}

def action (idx : Fin w) (next : Option Bool) (dir : Dir3) (si : Γ) (sw : Fin w → Γ) (so : Γ) :
    Option Bool × (Fin w → Γw) × Γw × Dir3 × (Fin w → Dir3) × Dir3 :=
  (next, (fun j => if j = idx then .blank else readBackWrite (sw j)), readBackWrite so, idleDir si,
    (fun j => if j = idx then dir else idleDir (sw j)), idleDir so)

theorem action_right (idx : Fin w) (next : Option Bool) (dir : Dir3) (si : Γ) (sw : Fin w → Γ) (so : Γ)
    (hne : sw idx ≠ Γ.start) :
    let (_, _, _, di, dw, dout) := action idx next dir si sw so
    (si = Γ.start → di = .right) ∧ (∀ j, sw j = Γ.start → dw j = .right) ∧ (so = Γ.start → dout = .right) := by
  refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
  intro j hj
  by_cases he : j = idx
  · subst j; exact False.elim (hne hj)
  · change (if j = idx then dir else idleDir (sw j)) = .right
    rw [ite_eq_right he]
    exact idleDir_right_of_start hj

def machine (idx : Fin w) : TM w where
  Q := Option Bool
  qstart := some false
  qhalt := none
  δ q si sw so := match q, sw idx with
    | some false, .blank => action idx (some true) .left si sw so
    | some true, .one => action idx none .stay si sw so
    | _, _ => allReadBack none si sw so
  δ_right_of_start q si sw so := by
    cases q with
    | none => exact rightOfStart_allReadBack si sw so
    | some b =>
      cases b <;> cases hr : sw idx <;> first
        | exact action_right idx (some true) .left si sw so (by simp only [hr, ne_eq, reduceCtorEq, not_false_eq_true])
        | exact action_right idx none .stay si sw so (by simp only [hr, ne_eq, reduceCtorEq, not_false_eq_true])
        | exact rightOfStart_allReadBack si sw so

theorem action_step (idx : Fin w) (next : Option Bool) (dir : Dir3) (c : Cfg w (machine idx).Q)
    (hs : c.state ≠ (machine idx).qhalt)
    (hδ : (machine idx).δ c.state c.input.read (fun j => (c.work j).read) c.output.read =
      action idx next dir c.input.read (fun j => (c.work j).read) c.output.read)
    (hi : c.input.read ≠ Γ.start) (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    (machine idx).step c = some ⟨next, c.input,
      Function.update c.work idx ((c.work idx).writeAndMove Γ.blank dir), c.output⟩ := by
  rw [TM.step, ite_eq_right hs, hδ]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · exact transitionInput_eq_self hi
  · funext j
    by_cases hj : j = idx
    · subst j; simp
    · simpa [action, hj, transitionTape] using transitionTape_eq_self (hw j)
  · exact transitionTape_eq_self ho

theorem erase_last (v : ℕ) : Function.update (regCells (v + 1)) (v + 1) Γ.blank = regCells v := by
  rw [← regCells_update_succ, Function.update_idem]
  rw [← regCells_blank (v := v) (j := v + 1) le_rfl, Function.update_eq_self]

theorem run (idx : Fin w) (v : ℕ) (c : Cfg w (machine idx).Q) (hs : c.state = some false)
    (ht : c.work idx = ⟨v + 2, regCells (v + 1)⟩)
    (hi : c.input.read ≠ Γ.start) (hw : ∀ j, (c.work j).read ≠ Γ.start) (ho : c.output.read ≠ Γ.start) :
    ∃ d, (machine idx).reachesIn 2 c d ∧ (machine idx).halted d ∧
      d.input = c.input ∧ d.output = c.output ∧ d.work idx = ⟨v + 1, regCells v⟩ ∧
      (∀ j, j ≠ idx → d.work j = c.work j) := by
  have hread : (c.work idx).read = Γ.blank := by rw [ht]; exact regCells_blank le_rfl
  have hfirst : (c.work idx).writeAndMove Γ.blank .left = ⟨v + 1, regCells (v + 1)⟩ := by
    rw [ht]
    simp only [Tape.writeAndMove, Tape.write, show ¬ v + 2 = 0 by omega, ↓reduceIte, Tape.move,
      ← regCells_blank (v := v + 1) (j := v + 2) le_rfl, Function.update_eq_self,
      show v + 2 - 1 = v + 1 by omega]
  let c₁ : Cfg w (machine idx).Q := ⟨some true, c.input, Function.update c.work idx ⟨v + 1, regCells (v + 1)⟩, c.output⟩
  have hstep : (machine idx).step c = some c₁ := by
    have hh := action_step idx (some true) .left c (by simp [machine, hs])
      (by simp only [machine, hs, hread]) hi hw ho
    simpa only [hfirst] using hh
  have ht₁ : c₁.work idx = ⟨v + 1, regCells (v + 1)⟩ := Function.update_self _ _ _
  have hr₁ : (c₁.work idx).read = Γ.one := by
    rw [ht₁]
    change regCells (v + 1) (v + 1) = Γ.one
    exact regCells_one (by omega) le_rfl
  have hclear : (c₁.work idx).writeAndMove Γ.blank .stay = ⟨v + 1, regCells v⟩ := by
    rw [ht₁]
    simp only [Tape.writeAndMove, Tape.write, Nat.add_one_ne_zero, ↓reduceIte, Tape.move, erase_last]
  have hw₁ : ∀ j, (c₁.work j).read ≠ Γ.start := by
    intro j
    by_cases hj : j = idx
    · subst j; rw [hr₁]; decide
    · simpa only [c₁, Function.update_of_ne hj] using hw j
  let d : Cfg w (machine idx).Q := ⟨none, c.input, Function.update c₁.work idx ⟨v + 1, regCells v⟩, c.output⟩
  have hstep₁ : (machine idx).step c₁ = some d := by
    have hh := action_step idx none .stay c₁ (by simp [machine, c₁])
      (by simp only [machine, c₁, hr₁]) hi hw₁ ho
    simpa only [hclear] using hh
  exact ⟨d, .step hstep (.step hstep₁ .zero), rfl, rfl, rfl, Function.update_self _ _ _,
    fun j hj => (Function.update_of_ne hj _ _).trans (Function.update_of_ne hj _ _)⟩

end JointThermoComplexity.Complexity.UnaryTrimMachine

#print axioms JointThermoComplexity.Complexity.UnaryTrimMachine.run
