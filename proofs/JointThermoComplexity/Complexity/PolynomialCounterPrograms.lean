module
public import proofs.JointThermoComplexity.Complexity.BoundedCounterFP

set_option autoImplicit false
@[expose] public section

/-! Every fixed natural polynomial has a literal three-register program and
an actual FP unary-output implementation on binary inputs. Coefficient lists
are fixed before input is read. -/

namespace JointThermoComplexity.Complexity.PolynomialCounters
open _root_.Complexity
open DInstabilityComplexity.MachineConstruction

variable {n : ℕ}

theorem eval_append (p q : CounterProgram n) (v : Fin n → ℕ) :
    counterProgramEval (p ++ q) v = counterProgramEval q (counterProgramEval p v) := by
  induction p generalizing v with
  | nil => rfl
  | cons i p ih => exact ih (i.eval v)

theorem increments_eval (r : Fin n) (c : ℕ) (v : Fin n → ℕ) :
    counterProgramEval (List.replicate c (.increment r)) v = Function.update v r (v r + c) := by
  induction c generalizing v with
  | zero => simp only [List.replicate_zero, counterProgramEval, Nat.add_zero, Function.update_eq_self]
  | succ c ih =>
    rw [List.replicate_succ, counterProgramEval, ih]
    simp only [CounterInstruction.eval, Function.update_self, Function.update_idem]
    congr 1
    omega

def value : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, L => c + L * value cs L

def step (c : ℕ) : CounterProgram 3 :=
  [.clear 2, .mulAdd 0 1 2 (by decide) (by decide) (by decide), .copy 2 1 (by decide)] ++
    List.replicate c (.increment 1)

theorem step_eval (c : ℕ) (v : Fin 3 → ℕ) :
    counterProgramEval (step c) v 0 = v 0 ∧ counterProgramEval (step c) v 1 = c + v 0 * v 1 := by
  rw [step, eval_append, increments_eval]
  norm_num [counterProgramEval, CounterInstruction.eval, Function.update_apply]
  omega

def program : List ℕ → CounterProgram 3
  | [] => [.clear 1]
  | c :: cs => program cs ++ step c

theorem program_eval (cs : List ℕ) (v : Fin 3 → ℕ) :
    counterProgramEval (program cs) v 0 = v 0 ∧ counterProgramEval (program cs) v 1 = value cs (v 0) := by
  induction cs with
  | nil => norm_num [program, value, counterProgramEval, CounterInstruction.eval, Function.update_apply]
  | cons c cs ih =>
    rw [program, eval_append]
    have hs := step_eval c (counterProgramEval (program cs) v)
    refine ⟨hs.1.trans ih.1, ?_⟩
    rw [hs.2, ih.1, ih.2]
    rfl

def word (cs : List ℕ) (input : List Bool) : List Bool := List.replicate (value cs input.length) true ++ [false]

theorem output_eq (cs : List ℕ) : BoundedCounters.output (program cs) 0 1 = word cs := by
  funext input
  rw [BoundedCounters.output, (program_eval cs (BoundedCounters.initialValues 0 input.length)).2]
  simp only [word, BoundedCounters.initialValues, Function.update_self]

theorem word_mem_FP (cs : List ℕ) : word cs ∈ FP := by
  rw [← output_eq]
  exact BoundedCounters.output_mem_FP (program cs) 0 1

end JointThermoComplexity.Complexity.PolynomialCounters

#print axioms JointThermoComplexity.Complexity.PolynomialCounters.program_eval
#print axioms JointThermoComplexity.Complexity.PolynomialCounters.word_mem_FP
