module
public import proofs.JointThermoComplexity.Complexity.AndCursor

set_option autoImplicit false
@[expose] public section

/-! Initialize one field-status cell without consuming input or output. -/

namespace JointThermoComplexity.Complexity.WriteStatus
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt

variable {n : ℕ}

def machine (dst : Fin n) (value : Bool) : TM n where
  Q := Bool
  qstart := false
  qhalt := true
  δ _ si sw so :=
    (true, fun j => if j = dst then Γw.ofBool value else readBackWrite (sw j),
      readBackWrite so, idleDir si, fun j => idleDir (sw j), idleDir so)
  δ_right_of_start _ _si _sw _so :=
    ⟨idleDir_right_of_start, fun _ h => idleDir_right_of_start h, idleDir_right_of_start⟩

theorem step (dst : Fin n) (value : Bool) (c : Cfg n Bool) (hs : c.state = false)
    (hi : c.input.read ≠ Γ.start) (ho : c.output.read ≠ Γ.start)
    (hw : ∀ j, (c.work j).read ≠ Γ.start) :
    (machine dst value).step c = some {
      state := true, input := c.input, work := ValidityAnd.writeFlag c.work dst value, output := c.output } := by
  simp only [TM.step, hs, machine, Bool.false_eq_true, ↓reduceIte]
  apply congrArg some
  apply Cfg.ext
  · rfl
  · exact transitionInput_eq_self hi
  · funext j
    change (c.work j).writeAndMove
      (if j = dst then Γw.ofBool value else readBackWrite (c.work j).read).toΓ
      (idleDir (c.work j).read) = Function.update c.work dst ((c.work dst).write (Γ.ofBool value)) j
    by_cases hj : j = dst
    · subst j
      rw [Function.update_self]
      simp only [↓reduceIte, Γw.ofBool_toΓ, idleDir, hw dst, ↓reduceIte, Tape.writeAndMove, Tape.move]
    · rw [Function.update_of_ne hj]
      simp only [ite_eq_right hj]
      exact transitionTape_eq_self (hw j)
  · exact transitionTape_eq_self ho

theorem hoareTime (dst : Fin n) (value : Bool) (before input emitted : List Bool)
    (R : (Fin n → Tape) → Prop)
    (hR : ∀ work work', (∀ j, j ≠ dst → work' j = work j) → R work → R work') :
    (machine dst value).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (work dst).head = 1 ∧ R work)
      (fun inp work out => Cursor before input emitted inp work out ∧
        (work dst).head = 1 ∧ (work dst).read = Γ.ofBool value ∧ R work) 1 := by
  rintro inp work out ⟨hc, hh, hr⟩
  let d : Cfg n Bool := ⟨true, inp, ValidityAnd.writeFlag work dst value, out⟩
  have hwork : ∀ j, j ≠ dst → d.work j = work j := fun j hj => ValidityAnd.writeFlag_other work dst j value hj
  have hhead : (d.work dst).head = 1 := (ValidityAnd.writeFlag_head work dst value).trans hh
  have hread : (d.work dst).read = Γ.ofBool value := ValidityAnd.writeFlag_read work dst value hh
  have hcursor : Cursor before input emitted d.input d.work d.output := by
    refine ⟨hc.cells, hc.head, ?_, hc.tapePrefix, hc.zero⟩
    intro j
    by_cases hj : j = dst
    · subst j
      refine ⟨?_, by rw [hhead]⟩
      rw [hread]
      exact Γ.ofBool_ne_start _
    · rw [hwork j hj]
      exact hc.works j
  exact ⟨d, 1, le_rfl, .step (step dst value ⟨false, inp, work, out⟩ rfl hc.input_read hc.output_read
    (fun j => (hc.works j).1)) .zero, rfl, hcursor, hhead, hread, hR work d.work hwork hr⟩

end JointThermoComplexity.Complexity.WriteStatus

#print axioms JointThermoComplexity.Complexity.WriteStatus.hoareTime
