module
public import proofs.JointThermoComplexity.Complexity.OutputProgram

set_option autoImplicit false
@[expose] public section

/-! Exact static templates for input-copy and negation gate equations. -/

namespace JointThermoComplexity.Complexity.UnaryGateOutput
open _root_.Complexity
open _root_.Complexity.TM
open HeaderAt BinaryIncrementRun RealSyntax OutputProgram

variable {w arity : ℕ}

def program (negate : Bool) (target source : Fin w) : List (Instruction w) :=
  [.word [false, true, false], .var target, .word (if negate then [true, false, false] else []), .var source]

def formula (negate : Bool) (values : Fin w → Fin arity) (target source : Fin w) : Formula arity :=
  .eq (.var (values target)) (if negate then .neg (.var (values source)) else .var (values source))

def timeBound (values : Fin w → ℕ) (target source : Fin w) : ℕ :=
  VariableOutput.timeBound (values target) + VariableOutput.timeBound (values source) + 10

theorem code_eq (negate : Bool) (values : Fin w → Fin arity) (target source : Fin w) :
    OutputProgram.code (fun j => (values j).val) (program negate target source) =
      (formula negate values target source).code := by
  cases negate <;> simp [program, OutputProgram.code, Instruction.code, formula, Formula.code, Term.code]

theorem time_le (negate : Bool) (values : Fin w → ℕ) (target source : Fin w) :
    OutputProgram.timeBound values (program negate target source) ≤ timeBound values target source := by
  cases negate <;> simp [program, OutputProgram.timeBound, Instruction.timeBound, timeBound] <;> omega

theorem valid (negate : Bool) (scratch target source : Fin w)
    (ht : target ≠ scratch) (hs : source ≠ scratch) : Valid (program negate target source) scratch := by
  intro instruction hi
  simp [program] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · trivial
  · exact ht
  · trivial
  · exact hs

theorem ready (negate : Bool) (values : Fin w → ℕ) (work : Fin w → Tape) (target source : Fin w)
    (ht : IsReg (values target) (work target)) (hs : IsReg (values source) (work source)) :
    Ready (program negate target source) values work := by
  intro instruction hi
  simp [program] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · trivial
  · exact ht
  · trivial
  · exact hs

def machine (negate : Bool) (scratch target source : Fin w) : TM w :=
  OutputProgram.machine scratch (program negate target source)

theorem hoareTime (negate : Bool) (scratch target source : Fin w) (ht : target ≠ scratch) (hs : source ≠ scratch)
    (values : Fin w → Fin arity) (before input emitted : List Bool) (R : (Fin w → Tape) → Prop) :
    (machine negate scratch target source).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        Register 0 (work scratch) ∧ IsReg (values target).val (work target) ∧ IsReg (values source).val (work source) ∧ R work)
      (fun inp work out => Cursor before input (emitted ++ (formula negate values target source).code) inp work out ∧
        (∀ j, Parked (work j)) ∧ Register 0 (work scratch) ∧
        IsReg (values target).val (work target) ∧ IsReg (values source).val (work source) ∧ R work)
      (timeBound (fun j => (values j).val) target source) := by
  rintro inp work out ⟨hc, hsafe, hb, htarget, hsource, hR⟩
  obtain ⟨d, t, htime, hreach, hhalt, hdcur, hdsafe, hdscratch, hdready, hdR⟩ :=
    OutputProgram.hoareTime scratch (program negate target source) (fun j => (values j).val)
      (valid negate scratch target source ht hs) before input emitted R inp work out
      ⟨hc, hsafe, hb, ready negate _ _ _ _ htarget hsource, hR⟩
  exact ⟨d, t, htime.trans (time_le negate _ _ _), hreach, hhalt,
    by simpa only [code_eq] using hdcur, hdsafe, hdscratch,
    hdready (.var target) (by simp [program]), hdready (.var source) (by simp [program]), hdR⟩

end JointThermoComplexity.Complexity.UnaryGateOutput

#print axioms JointThermoComplexity.Complexity.UnaryGateOutput.hoareTime
