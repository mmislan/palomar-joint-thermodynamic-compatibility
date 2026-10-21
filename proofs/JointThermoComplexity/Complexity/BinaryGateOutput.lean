module
public import proofs.JointThermoComplexity.Complexity.OutputProgram

set_option autoImplicit false
@[expose] public section

/-! Exact static templates for addition and multiplication gate equations. -/

namespace JointThermoComplexity.Complexity.BinaryGateOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax
open OutputProgram

variable {w arity : ℕ}

def program (multiply : Bool) (target left right : Fin w) : List (Instruction w) :=
  [.word [false, true, false], .var target,
    .word (if multiply then [false, true, true] else [false, true, false]), .var left, .var right]

def formula (multiply : Bool) (values : Fin w → Fin arity) (target left right : Fin w) : Formula arity :=
  .eq (.var (values target))
    (if multiply then .mul (.var (values left)) (.var (values right)) else .add (.var (values left)) (.var (values right)))

def timeBound (values : Fin w → ℕ) (target left right : Fin w) : ℕ :=
  VariableOutput.timeBound (values target) + VariableOutput.timeBound (values left) +
    VariableOutput.timeBound (values right) + 11

theorem code_eq (multiply : Bool) (values : Fin w → Fin arity) (target left right : Fin w) :
    OutputProgram.code (fun j => (values j).val) (program multiply target left right) =
      (formula multiply values target left right).code := by
  cases multiply <;> simp [program, OutputProgram.code, Instruction.code, formula, Formula.code, Term.code]

theorem time_eq (multiply : Bool) (values : Fin w → ℕ) (target left right : Fin w) :
    OutputProgram.timeBound values (program multiply target left right) = timeBound values target left right := by
  cases multiply <;> simp [program, OutputProgram.timeBound, Instruction.timeBound, timeBound] <;> omega

theorem valid (multiply : Bool) (scratch target left right : Fin w)
    (ht : target ≠ scratch) (hl : left ≠ scratch) (hr : right ≠ scratch) :
    Valid (program multiply target left right) scratch := by
  intro instruction hi
  simp [program] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · trivial
  · exact ht
  · trivial
  · exact hl
  · exact hr

theorem ready (multiply : Bool) (values : Fin w → ℕ) (work : Fin w → Tape) (target left right : Fin w)
    (ht : IsReg (values target) (work target)) (hl : IsReg (values left) (work left)) (hr : IsReg (values right) (work right)) :
    Ready (program multiply target left right) values work := by
  intro instruction hi
  simp [program] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · trivial
  · exact ht
  · trivial
  · exact hl
  · exact hr

def machine (multiply : Bool) (scratch target left right : Fin w) : TM w :=
  OutputProgram.machine scratch (program multiply target left right)

theorem hoareTime (multiply : Bool) (scratch target left right : Fin w)
    (ht : target ≠ scratch) (hl : left ≠ scratch) (hr : right ≠ scratch)
    (values : Fin w → Fin arity) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine multiply scratch target left right).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work scratch) ∧ IsReg (values target).val (work target) ∧
        IsReg (values left).val (work left) ∧ IsReg (values right).val (work right) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (formula multiply values target left right).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧ IsReg (values target).val (work target) ∧
        IsReg (values left).val (work left) ∧ IsReg (values right).val (work right) ∧ R work)
      (timeBound (fun j => (values j).val) target left right) := by
  rintro inp work out ⟨hc, hs, hb, htarget, hleft, hright, hR⟩
  obtain ⟨d, t, htime, hreach, hhalt, hdcur, hdsafe, hdscratch, hdready, hdR⟩ :=
    OutputProgram.hoareTime scratch (program multiply target left right) (fun j => (values j).val)
      (valid multiply scratch target left right ht hl hr) before input emitted R inp work out
      ⟨hc, hs, hb, ready multiply _ _ _ _ _ htarget hleft hright, hR⟩
  refine ⟨d, t, by simpa only [time_eq] using htime, hreach, hhalt,
    by simpa only [code_eq] using hdcur, hdsafe, hdscratch, ?_, ?_, ?_, hdR⟩
  · exact hdready (.var target) (by simp [program])
  · exact hdready (.var left) (by simp [program])
  · exact hdready (.var right) (by simp [program])

end JointThermoComplexity.Complexity.BinaryGateOutput

#print axioms JointThermoComplexity.Complexity.BinaryGateOutput.hoareTime
