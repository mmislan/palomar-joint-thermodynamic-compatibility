module
public import proofs.JointThermoComplexity.Complexity.OutputProgram

set_option autoImplicit false
@[expose] public section

/-! A fixed leading and trailing around one variable term with a runtime address. -/

namespace JointThermoComplexity.Complexity.SingleVariableOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax OutputProgram

variable {w arity : ℕ}

def program (source : Fin w) (leading trailing : List Bool) : List (Instruction w) :=
  [.word leading, .var source, .word trailing]

def machine (scratch source : Fin w) (leading trailing : List Bool) : TM w :=
  OutputProgram.machine scratch (program source leading trailing)

theorem code_eq (source : Fin w) (leading trailing : List Bool) (idx : Fin arity) :
    OutputProgram.code (fun _ => idx.val) (program source leading trailing) = leading ++ (Term.var idx).code ++ trailing := by
  simp [program, OutputProgram.code, Instruction.code, Term.code]

theorem time_eq (source : Fin w) (leading trailing : List Bool) (v : ℕ) :
    OutputProgram.timeBound (fun _ => v) (program source leading trailing) =
      leading.length + VariableOutput.timeBound v + trailing.length + 3 := by
  simp only [program, OutputProgram.timeBound, Instruction.timeBound]
  omega

theorem valid (scratch source : Fin w) (hne : source ≠ scratch) (leading trailing : List Bool) :
    Valid (program source leading trailing) scratch := by
  intro instruction hi
  simp [program] at hi
  rcases hi with rfl | rfl | rfl
  · trivial
  · exact hne
  · trivial

theorem ready (source : Fin w) (leading trailing : List Bool) (v : ℕ) (work : Fin w → Tape)
    (h : IsReg v (work source)) : Ready (program source leading trailing) (fun _ => v) work := by
  intro instruction hi
  simp [program] at hi
  rcases hi with rfl | rfl | rfl
  · trivial
  · exact h
  · trivial

theorem hoareTime (scratch source : Fin w) (hne : source ≠ scratch) (idx : Fin arity)
    (before input emitted leading trailing : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine scratch source leading trailing).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work scratch) ∧ IsReg idx.val (work source) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (leading ++ (Term.var idx).code ++ trailing)) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧ IsReg idx.val (work source) ∧ R work)
      (leading.length + VariableOutput.timeBound idx.val + trailing.length + 3) := by
  rintro inp work out ⟨hc, hs, hb, hr, hR⟩
  obtain ⟨d, t, ht, hreach, hhalt, hdcur, hdsafe, hdscratch, hdready, hdR⟩ :=
    OutputProgram.hoareTime scratch (program source leading trailing) (fun _ => idx.val)
      (valid scratch source hne leading trailing) before input emitted R inp work out
      ⟨hc, hs, hb, ready source leading trailing idx.val work hr, hR⟩
  exact ⟨d, t, by simpa only [time_eq] using ht, hreach, hhalt,
    by simpa only [code_eq] using hdcur, hdsafe, hdscratch, hdready (.var source) (by simp [program]), hdR⟩

end JointThermoComplexity.Complexity.SingleVariableOutput

#print axioms JointThermoComplexity.Complexity.SingleVariableOutput.hoareTime
