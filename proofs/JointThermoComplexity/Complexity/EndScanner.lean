module
public import proofs.JointThermoComplexity.Complexity.ScannerSpec

set_option autoImplicit false
@[expose] public section

/-! One actual step rejects trailing input without losing earlier failures. -/

namespace JointThermoComplexity.Complexity.EndScanner
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {w : ℕ}

def accepted (status input : Γ) : Bool := (status == Γ.one) && (input == Γ.blank)

def machine (master : Fin w) : TM w where
  Q := Bool
  qstart := false
  qhalt := true
  δ _ si sw so :=
    (true, fun j => if j = master then Γw.ofBool (accepted (sw master) si) else readBackWrite (sw j),
      readBackWrite so, idleDir si, fun j => idleDir (sw j), idleDir so)
  δ_right_of_start _ _si _sw _so :=
    ⟨idleDir_right_of_start, fun _ h => idleDir_right_of_start h, idleDir_right_of_start⟩

theorem cursor_read {before input emitted : List Bool} {inp out : Tape} {work : Fin w → Tape}
    (hc : Cursor before input emitted inp work out) (initial : Bool) :
    accepted (Γ.ofBool initial) inp.read = (initial && input.isEmpty) := by
  cases input with
  | nil =>
    have hr : inp.read = Γ.blank := by
      simp [Tape.read, hc.head, hc.cells, Tape.init_ofBool_cells_ge before before.length le_rfl]
    cases initial <;> simp [accepted, hr, Γ.ofBool]
  | cons bit rest =>
    have hindex : before.length < (before ++ bit :: rest).length := by simp
    have hr : inp.read = Γ.ofBool bit := by
      rw [Tape.read, hc.head, hc.cells, Tape.init_ofBool_cells_lt _ before.length hindex]
      simp
    cases initial <;> cases bit <;> simp [accepted, hr, Γ.ofBool]

theorem step (master : Fin w) (c : Cfg w Bool) (hs : c.state = false)
    (hi : c.input.read ≠ Γ.start) (ho : c.output.read ≠ Γ.start)
    (hw : ∀ j, (c.work j).read ≠ Γ.start) :
    (machine master).step c = some {
      state := true, input := c.input,
      work := ValidityAnd.writeFlag c.work master (accepted (c.work master).read c.input.read), output := c.output } := by
  simp only [TM.step, hs, machine, Bool.false_eq_true, ↓reduceIte]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · exact transitionInput_eq_self hi
  · funext j
    change (c.work j).writeAndMove
      (if j = master then Γw.ofBool (accepted (c.work master).read c.input.read) else readBackWrite (c.work j).read).toΓ
      (idleDir (c.work j).read) = Function.update c.work master
        ((c.work master).write (Γ.ofBool (accepted (c.work master).read c.input.read))) j
    by_cases hj : j = master
    · subst j
      rw [Function.update_self]
      simp only [↓reduceIte, Γw.ofBool_toΓ, idleDir, hw master, ↓reduceIte, Tape.writeAndMove, Tape.move]
    · rw [Function.update_of_ne hj]
      simp only [ite_eq_right hj]
      exact transitionTape_eq_self (hw j)
  · exact transitionTape_eq_self ho

theorem hoareTime (master : Fin w) (initial : Bool) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ master → work' j = work j) → R work → R work') :
    (machine master).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work master).head = 1 ∧ (work master).read = Γ.ofBool initial ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work master).head = 1 ∧ (work master).read = Γ.ofBool (initial && input.isEmpty) ∧ R work) 1 := by
  rintro inp work out ⟨hc, hh, hv, hr⟩
  have hacc : accepted (work master).read inp.read = (initial && input.isEmpty) := by
    rw [hv]
    exact cursor_read hc initial
  let d : Cfg w Bool := ⟨true, inp, ValidityAnd.writeFlag work master (initial && input.isEmpty), out⟩
  have hstep : (machine master).step ⟨false, inp, work, out⟩ = some d := by
    have he := step master ⟨false, inp, work, out⟩ rfl hc.input_read hc.output_read (fun j => (hc.works j).1)
    change (machine master).step ⟨false, inp, work, out⟩ = some
      (⟨true, inp, ValidityAnd.writeFlag work master (accepted (work master).read inp.read), out⟩ : Cfg w Bool) at he
    rw [hacc] at he
    exact he
  have hother : ∀ j, j ≠ master → d.work j = work j :=
    fun j hj => ValidityAnd.writeFlag_other work master j (initial && input.isEmpty) hj
  have hhead : (d.work master).head = 1 := (ValidityAnd.writeFlag_head work master (initial && input.isEmpty)).trans hh
  have hread : (d.work master).read = Γ.ofBool (initial && input.isEmpty) :=
    ValidityAnd.writeFlag_read work master (initial && input.isEmpty) hh
  have hcursor : Cursor before input emitted d.input d.work d.output := by
    refine ⟨hc.cells, hc.head, ?_, hc.tapePrefix, hc.zero⟩
    intro j
    by_cases hj : j = master
    · subst j
      refine ⟨?_, by rw [hhead]⟩
      rw [hread]
      exact Γ.ofBool_ne_start _
    · rw [hother j hj]
      exact hc.works j
  exact ⟨d, 1, le_rfl, .step hstep .zero, rfl, hcursor, hhead, hread, hR work d.work hother hr⟩

end JointThermoComplexity.Complexity.EndScanner

#print axioms JointThermoComplexity.Complexity.EndScanner.hoareTime
