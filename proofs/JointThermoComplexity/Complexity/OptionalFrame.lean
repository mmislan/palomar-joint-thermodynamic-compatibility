module
public import proofs.JointThermoComplexity.Complexity.OptionalMachine

set_option autoImplicit false
@[expose] public section

/-! The complete two-status-tape frame for optional-tag termination. -/

namespace JointThermoComplexity.Complexity.OptionalFrame
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt OptionalMachine

variable {w : ℕ}

theorem other (work : Fin w → Tape) (master flag : Fin w) (good : Bool) (j : Fin w)
    (hjf : j ≠ flag) (hjm : j ≠ master) (hw : (work j).read ≠ Γ.start) :
    taggedWork work master flag good j = work j := by
  rw [taggedWork, ite_eq_right hjf]
  simp only [hjm, and_false, ↓reduceIte]
  exact transitionTape_eq_self hw

theorem flag_head (work : Fin w → Tape) (master flag : Fin w) (good : Bool)
    (hw : (work flag).read ≠ Γ.start) (hh : (work flag).head = 1) :
    (taggedWork work master flag good flag).head = 1 := by
  simp [taggedWork, idleDir, hw, Tape.writeAndMove, Tape.move, Tape.write_head, hh]

theorem flag_read (work : Fin w → Tape) (master flag : Fin w) (good : Bool)
    (hw : (work flag).read ≠ Γ.start) (hh : (work flag).head = 1) :
    (taggedWork work master flag good flag).read = Γ.ofBool good := by
  have hn : (work flag).cells 1 ≠ Γ.start := by simpa only [Tape.read, hh] using hw
  simp [taggedWork, idleDir, Tape.read, Tape.writeAndMove, Tape.move, Tape.write, hh, hn]

theorem master_good (work : Fin w → Tape) (master flag : Fin w) (hm : master ≠ flag)
    (hw : (work master).read ≠ Γ.start) : taggedWork work master flag true master = work master := by
  simp only [taggedWork, hm, ↓reduceIte, Bool.true_eq_false, false_and]
  exact transitionTape_eq_self hw

theorem master_bad_head (work : Fin w → Tape) (master flag : Fin w) (hm : master ≠ flag)
    (hw : (work master).read ≠ Γ.start) (hh : (work master).head = 1) :
    (taggedWork work master flag false master).head = 1 := by
  simp [taggedWork, hm, idleDir, hw, Tape.writeAndMove, Tape.move, Tape.write_head, hh]

theorem master_bad_read (work : Fin w → Tape) (master flag : Fin w) (hm : master ≠ flag)
    (hw : (work master).read ≠ Γ.start) (hh : (work master).head = 1) :
    (taggedWork work master flag false master).read = Γ.zero := by
  have hn : (work master).cells 1 ≠ Γ.start := by simpa only [Tape.read, hh] using hw
  simp [taggedWork, hm, idleDir, Tape.read, Tape.writeAndMove, Tape.move, Tape.write, hh, hn]

theorem cursor {before input emitted : List Bool} {inp out : Tape} {work : Fin w → Tape}
    (hc : Cursor before input emitted inp work out) (master flag : Fin w) (hm : master ≠ flag)
    (good : Bool) (hf : (work flag).head = 1) (hmaster : (work master).head = 1) :
    Cursor before input emitted inp (taggedWork work master flag good) out := by
  refine ⟨hc.cells, hc.head, ?_, hc.tapePrefix, hc.zero⟩
  intro j
  by_cases hjf : j = flag
  · subst j
    refine ⟨?_, by rw [flag_head work master flag good (hc.works flag).1 hf]⟩
    rw [flag_read work master flag good (hc.works flag).1 hf]
    exact Γ.ofBool_ne_start _
  · by_cases hjm : j = master
    · subst j
      cases good with
      | true => rw [master_good work master flag hm (hc.works master).1]; exact hc.works master
      | false =>
        refine ⟨?_, by rw [master_bad_head work master flag hm (hc.works master).1 hmaster]⟩
        rw [master_bad_read work master flag hm (hc.works master).1 hmaster]
        decide
    · rw [other work master flag good j hjf hjm (hc.works j).1]
      exact hc.works j

end JointThermoComplexity.Complexity.OptionalFrame

#print axioms JointThermoComplexity.Complexity.OptionalFrame.cursor
