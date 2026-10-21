module
public import proofs.JointThermoComplexity.Complexity.StrictGeneratedTemplates
public import proofs.JointThermoComplexity.Complexity.RowSquareCanonical

set_option autoImplicit false
@[expose] public section

/-! Actual fixed-program output for the generated strict sections. Each
program uses two raw address buffers and emits entries without a polynomial
terminator; its runtime is the checked fixed-word program's linear bound.
-/

namespace JointThermoComplexity.Complexity.StrictGeneratedBytes
open _root_.Complexity _root_.Complexity.TM StrictGeneratedTemplates WordPolynomialProgram
open HeaderAt (Cursor)
variable {w : ℕ}

def program (kind : Kind) : List (WordCodeProgram.Instr 2) := entries (template kind)

theorem output_code (values : Fin 2 → ℕ) (kind : Kind) :
    WordCodeProgram.output (fun i => (values i).bits) (program kind) = RowSquareCanonical.entries (data values kind) := by
  have h := entries_complete (fun i => (values i).bits) (template kind)
  have hn := RowSquareCanonical.entries_polynomial (data values kind)
  have hf : refCode (fun i => (values i).bits) = BitCodec.naturalCode ∘ refValue values := by
    funext r
    exact refCode_natural values r
  rw [hf] at h
  unfold data at hn
  rw [NumberedTermEquations.relabel_comp] at hn
  exact List.append_cancel_right (h.trans hn.symm)

def machine (ports : Fin 2 → Fin w) (kind : Kind) : TM w := WordCodeProgram.machine ports (program kind)
def timeBound (W : ℕ) (kind : Kind) : ℕ := WordCodeProgram.timeBound W (program kind)

theorem hoareTime (ports : Fin 2 → Fin w) (values : Fin 2 → ℕ) (W : ℕ)
    (hW : ∀ i, (values i).bits.length ≤ W) (kind : Kind) (before input emitted : List Bool)
    (R : (Fin w → Tape) → Prop) :
    (machine ports kind).HoareTime
      (fun inp work out => Cursor before input emitted inp work out ∧ (∀ j, Parked (work j)) ∧
        WordCodeProgram.Ready ports (fun i => (values i).bits) R work)
      (fun inp work out => Cursor before input (emitted ++ RowSquareCanonical.entries (data values kind)) inp work out ∧
        (∀ j, Parked (work j)) ∧ WordCodeProgram.Ready ports (fun i => (values i).bits) R work)
      (timeBound W kind) := by
  have ho : WordCodeProgram.output (fun i => (values i).bits) (entries (template kind)) =
      RowSquareCanonical.entries (data values kind) := output_code values kind
  simpa only [machine, timeBound, program, ho] using
    entries_hoareTime ports (fun i => (values i).bits) W hW (template kind) before input emitted R

noncomputable def timePolynomial (kind : Kind) : Polynomial ℕ := WordPolynomialProgram.timePolynomial (program kind)

theorem timePolynomial_eval (kind : Kind) (W : ℕ) : (timePolynomial kind).eval W = timeBound W kind :=
  WordPolynomialProgram.timePolynomial_eval (program kind) W

end JointThermoComplexity.Complexity.StrictGeneratedBytes

#print axioms JointThermoComplexity.Complexity.StrictGeneratedBytes.output_code
#print axioms JointThermoComplexity.Complexity.StrictGeneratedBytes.hoareTime
#print axioms JointThermoComplexity.Complexity.StrictGeneratedBytes.timePolynomial_eval
